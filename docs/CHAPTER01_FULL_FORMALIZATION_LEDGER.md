# Chapter01_full.pdf Formalization Ledger

Source: `references/Chapter01_full.pdf`

Focused bottleneck ledger:
[`CHAPTER01_REVERSE_SUMMATION_BOTTLENECK.md`](CHAPTER01_REVERSE_SUMMATION_BOTTLENECK.md)

Audit date: 2026-06-11

PDF identity:

- SHA256: `e8711edc57f9c9c519de7137ac29454953f43ad8eb98adcb20652dd602f49df7`
- `pdfinfo references/Chapter01_full.pdf` reported 38 pages.
- `pdftotext -layout` produced `/private/tmp/chapter01_full_layout.txt`
  with 1614 lines.
- `pdftotext` produced `/private/tmp/chapter01_full_plain.txt` with 1683
  lines.

## Closure Summary

Status: **INCOMPLETE for the full local PDF**.

The earlier ledger `CHAPTER01_FORMALIZATION_LEDGER.md` closes only the local
six-page `references/Chapter01.pdf` excerpt through the opening of Section 1.3.
The full 38-page PDF has additional Chapter 1 definitions, examples, algorithms,
Lemma 1.1, and Problems 1.1--1.10.

This pass closed the foundational gaps that were directly reusable across the
full chapter:

- forward-error predicates for scalar and vector problems;
- normwise vector backward-error and condition-number-bound predicates, plus
  the finite-vector normwise `forward error <= condition number * backward error`
  theorem;
- mixed forward-backward error predicates for scalar and vector problems;
- numerical-stability and forward-stability comparison predicates;
- corrected the local stability comments from the old §1.7--§1.9 label to the
  full-PDF §1.5--§1.6 placement;
- exact cancellation algebra and the relative-error amplification factor from
  Section 1.7;
- the rationalized ten-significant-figure trigonometric cancellation example
  from Section 1.7, including the direct `25/36` scaled value and rewritten
  `1/2` scaled value;
- Higham Lemma 1.1 in the repository's operator-2 predicate form, including
  the rank-one perturbation witness and optimality/lower-bound direction.
- Problem 1.1's computed-denominator relative error, including both-way
  `E/(1+E)` lower envelopes and conditional `E/(1-E)` upper envelopes
  relating it to the standard exact-denominator relative error.
- Problem 1.2's near-integer table ambiguity: the stated one-ulp table
  error bars are consistent both with the nearby integer ending in `4` and
  with a value just below it whose integer part ends in `3`.
- Section 1.4's precision-versus-accuracy vocabulary: `AccuracyMeasure`
  selects absolute or relative error, `PrecisionMeasure` records unit
  roundoff, `BasicOperationPrecisionBounded` packages the primitive-operation
  precision contract, and a rounded scalar multiplication has relative
  accuracy bounded by the model precision when the exact product is nonzero.
- Problem 1.3's exact cancellation-avoiding rewrites for
  `sqrt(1+x)-1`, `sin x - sin y`, `x^2-y^2`,
  `(1-cos x)/sin x`, and the law-of-cosines square-root expression.
- Problem 1.4's stable complex square-root formulae, including the
  `0 <= a` branch `x=sqrt((r+a)/2), y=b/(2*x)`, the `a < 0` branch
  `y=sign(b)*sqrt((r-a)/2), x=b/(2*y)`, and the zero-input case.
- Problem 1.6's calculator upside-down word puzzle, including the digit-glyph
  map, all listed words, and the exact square-root entry
  `sqrt(31438449) = 5607`.
- exact quadratic-formula algebra for Section 1.8, including root correctness,
  sum/product identities, the `c/(a*x)` second-root recovery identity, the
  displayed `10^20` example roots, and the exact variable-scaling identity.
- the displayed Section 1.8 finite-range comparison for the first overflow
  example: the unscaled `b*b` intermediate overflows the IEEE single finite
  range, the same unscaled `b*b`, `4*a`, `4*a*c`, and exact discriminant are
  IEEE double normal-range quantities, the exact primitive double operations
  satisfy nearest/even normal-branch relative-error and no-flag wrappers, the
  actual rounded-intermediate double trace
  `fl(fl(b*b)-fl(fl(4*a)*c))` has normal-range, nearest/even standard-model,
  no-flag, and value-field wrappers, and
  the divided equation's `b*b`, `4*a*c`, and discriminant intermediates are
  IEEE single normal-range quantities.
- the rounded discriminant operation trace
  `fl(fl(b*b) - fl(fl(4*a)*c))`, with one local factor for each product and
  for the final subtraction.
- the rounded standard-formula branch micro-kernel with a supplied square-root
  value, proving each branch has a `gamma_3` relative-error factor around the
  corresponding exact quadratic-formula root.
- the supplied relative-error square-root input bridge for the quadratic
  formula: if `shat=s*(1+epsSqrt)` and `|epsSqrt| <= u`, each rounded branch
  is bounded by the explicit square-root perturbation term plus the later
  `gamma_3` branch-arithmetic factor.
- the abstract computed-square-root branch for the quadratic formula, using
  `FPModel.model_sqrt` on the exact discriminant and then the same `gamma_3`
  branch-arithmetic bound.
- the rounded two-operation recovery micro-kernel `fl(c / fl(a*xhat))`, with
  a `gamma_2` relative-error bound around `c/(a*xhat)`.
- Problem 1.8's Kahan-Muller recurrence at the exact-arithmetic layer:
  the displayed initial values, nonlinear recurrence, monotone convergence
  to `6`, the `x_34` four-significant-figure interval around `5.998`, a
  concrete four-significant-decimal display trace returning `100` at `x_34`,
  and the hidden `100^k` contamination mechanism that explains
  finite-precision drift, including a non-enumerative `c >= 1`, `k >= 2`
  dominance theorem and a concrete `c = 1`, `k = 34` witness whose hidden-mode
  ratio lies in `(99,100)` and hence within one unit of the spurious root
  `100`.
- the aggregate-level sample-variance cancellation example from Section 1.9:
  exact aggregates give variance `1`, while the collapsed one-pass aggregate
  pair gives value `0` and relative error `1`; Lean also proves a general
  aggregate sign criterion showing the one-pass aggregate formula is negative
  whenever the rounded aggregates satisfy `sumSq < sum^2/n`, plus the
  neighboring `[10000,10001,10002]` aggregate value `-1/2`.
- Problem 1.7's displayed sample-variance condition-number closed forms and
  first-order derivation layer: the mean is affine along perturbation lines,
  `V(x+t dx)` has the source linear directional coefficient plus a quadratic
  remainder, that coefficient is bounded by the displayed componentwise and
  normwise condition numbers under the corresponding perturbation budgets, the
  normwise forms agree, and the displayed componentwise closed form is bounded
  by the normwise one.
- Problem 1.10's exact perturbed-mean cancellation substrate for the two-pass
  sample variance: if the second pass uses any real mean `m`, the corrected sum
  of squares changes by exactly `n*(m-mean)^2`, so the mean error contributes
  quadratically before the remaining rounded operations are charged; the same
  substrate is also closed in exact relative-error form and as a one-factor
  rounded-transfer bound, with a weighted nonnegative-sum helper for collapsing
  componentwise squared-deviation perturbations into one aggregate relative
  factor, plus a fixed-supplied-mean floating-point second-pass theorem:
  rounded subtraction, squaring, recursive summation, and final division equal
  `sampleVarianceTwoPassWithMean x m * (1+theta)` with
  `|theta| <= gamma fp (n+3)`.  The computed first-pass mean is also closed as
  the exact mean of componentwise perturbed inputs with per-entry perturbations
  bounded by `gamma fp n`, with absolute error bounded by
  `gamma fp n` times the average absolute input size.  These pieces are
  composed into a true-variance relative-error theorem with the exact
  first-pass mean-error quadratic, then into a squared-`gamma fp n` first-pass
  contribution, and finally into a source-style linear-plus-remainder form:
  `(n+3)u` plus an explicit rational quadratic remainder and the squared-`γ_n`
  mean term; the named remainder is also bounded by an explicit quadratic
  envelope in `u` under `(n+3)u <= 1/2`.
- exact 2-by-2 Cramer algebra and the Problem 1.9 denominator-exact
  rounded-numerator-error-to-forward/residual-error bridge, including both
  displayed condition-number forms.
- the Section 1.11 single-rounding accumulation mechanism for
  `(1 + 1/n)^n`, proving that rounding the initial base multiplies the exact
  finite-`n` approximation by `(1+delta)^n`.
- the Problem 1.5 exact/log-error, supplied rounded-outer-exp, and finite
  round-to-even wrapper: `exp(n*log(1+1/n))` equals the exact finite-`n`
  approximation, a supplied relative log error `|epsLog| <= u` perturbs the
  exponent by at most `u`, a supplied final exp relative error gives total
  relative error at most `exp(u)*(1+u)-1`, and finite-normal
  `FloatingPointFormat.finiteRoundToEven` outputs instantiate those two
  supplied errors. The scalar envelope is also proved literally as `O(u)` as
  `u -> 0`.
- the Section 1.12.1 no-pivot LU example at the exact/modelled-rounding
  level, including the displayed inverse, `kappa_infty(A)=4/(1+epsilon)`,
  the reproduction error `[[0,0],[0,1]]` when
  `fl(1+epsilon^{-1}) = epsilon^{-1}`, a concrete IEEE-single
  `epsilon=2^{-24}` proof of that rounding, the exact partial-pivoting
  row-swap factorization `P*A=L*U` with multiplier bounded by one and a
  zero-perturbation pivoted LU backward-error certificate, and the concrete
  IEEE-single pivoted primitive trace whose rounded `U_22=-1` factors satisfy
  a componentwise pivoted LU backward-error certificate with radius `epsilon`.
- the exact Section 1.12.2 square-root/squaring loop baseline, proving that
  60 real square roots followed by 60 real squarings returns the original
  nonnegative input.
- the displayed Section 1.12.2 HP 48G surrogate function and compact
  root/square phase-law bridge, including the concrete `x=100` output `1`,
  relative error `99/100`, the derivation of the step surrogate from abstract
  phase laws, and full source-interval absolute/relative error formulas for
  `x >= 1`, `0 <= x < 1`, and `0 < x < 1`.
- the exact Section 1.12.3 inverse-square term-size baseline, proving that
  the `k = 4096` term is exactly `2^{-24}` and every later inverse-square
  term is no larger; Lean also proves that every `1/k^2` with
  `2897 <= k < 4096` lies strictly between one half-ulp and one ulp at
  binary32 exponent `1`, factors that interval into a reusable successor
  theorem for adjacent normalized mantissas, composes it through a recursive
  forward-accumulator induction, proves every intermediate prefix in the
  `k = 2897` through `k = 4095` below-plateau window, proves that those 1194
  additions carry the pre-window accumulator to the six-before-plateau
  accumulator, proves that the six additions from `k = 4091` through `k = 4096`
  carry the six-before-plateau accumulator into the plateau, certifies the
  integer mantissa-increment sum and bounded nearest-increment inequalities for
  terms `2` through `2896`, proves the source-rounding bridge for those
  nearest increments, proves the actual `k = 1` accumulator, and proves that
  the actual accumulator from zero reaches/stays at the plateau from `k = 4096`
  onward; Lean also models the reverse-order `N`-term accumulator and proves a
  source-shaped split of the `10^9`-term reverse run into the high-index prefix
  and final `4096` low-index terms.  Lean further proves the local binary32
  predecessor endpoints for `k = 4091`, `k = 4092`,
  `k = 4093`, `k = 4094`, and `k = 4095`, proves the
  nearest/even midpoint mechanism that adding the `k = 4096` term to the concrete immediately preceding
  binary32 accumulator rounds to the plateau, proves that adding the same term
  to the concrete even-mantissa plateau accumulator printed approximately as
  `1.64472532` rounds back to that same accumulator, and proves that every
  later positive `1/k^2` term rounds away once that plateau value has been
  reached.
- the Section 1.13 sine example exact substrate
  `x + 10^{-8} sin(2^{24}x)`, proving the perturbation from `x` has absolute
  value at most `10^{-8}`, and the contrived increasing-precision branch
  example at `x = 2/3`: exact arithmetic returns `1`, while the modeled else
  branch with rounded exponential value `1` returns `0` and has relative
  error `1`.
- the Section 1.14.1 exact Algorithm 2 baseline: with exact `exp` and `log`,
  Algorithm 2 computes the same branch function as Algorithm 1 for
  `(exp x - 1)/x`.
- the Section 1.14.1 Table 1.2 displayed finite data layer:
  `expm1Table12_x_rows`, `expm1Table12_algorithm1_rows`, and
  `expm1Table12_algorithm2_rows` encode the exact rational values printed in
  the table, with the missing `10^-16` Algorithm 2 entry represented by
  `none`; `expm1Table12_algorithm2_ten_pow_neg15_last_digit_correction`
  formalizes the source note that the `10^-15` Algorithm 2 row should end in
  `1`; and `expm1Page23_displayed_single_precision_ratio` plus
  `expm1Page23_displayed_exact_arithmetic_ratio` reduce the two immediately
  following displayed decimal ratios to exact rational ratios.
- the Section 1.14.1 displayed floating-point algebra through equation (1.9):
  the `yhat = 1` branch implies `x = -log(1+delta)`, and the `yhat != 1`
  branch has the displayed three-epsilon rounded subtraction/log/division
  form under the local `FPModel` laws and an explicit rounded-log input.
- a generic Section 1.14.1 `gamma_4` wrapper showing that the rounded
  Algorithm 2 core differs from `g(yhat)=(yhat-1)/log(yhat)` by one
  `1+theta` factor with `|theta| <= gamma_4`, under the local positivity and
  `gammaValid` guards, plus a `relError` version and a local budget comparing
  the rounded core back to `g(y)` when `yhat=y*(1+delta)`.
- a sharper Section 1.14.1 signed-product `gamma_3` wrapper:
  `expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma3`,
  `expm1Algorithm2RoundedCore_relError_le_gamma3`,
  `expm1Algorithm2RoundedCore_relError_le_local_bound_gamma3`,
  `expm1Algorithm2RoundedCore_relError_le_eta_add_gamma3`, and
  `expm1Algorithm2RoundedCore_relError_le_eta_add_gamma3_of_primitive_bounds`
  combine the three equation (1.9) local factors as a signed product, yielding
  the source-aligned `eta + (1+eta)*gamma_3` bridge from the same drift
  certificate. The corollaries
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_remainder`
  and
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_remainder_of_primitive_bounds`
  turn a drift bound of `(u/2)*|g(y)|` into the explicit first-order
  `3.5u` estimate plus the proved higher-order remainder
  `((3u)^2)/(1-3u) + (u/2)*gamma_3`. The local-remainder corollary
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_local_remainder_of_abs_bounds`
  derives the same leading term directly from `|delta| <= deltaAbs <= u`,
  leaving only the explicit slow-ratio remainder
  `S/|g(y)|*(1+gamma_3)` with
  `S = expm1Algorithm2PrimitiveSlowRemainderBound yAbs yhatAbs deltaAbs`.
  The radius wrapper
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_radius_remainder_of_abs_bounds`
  compresses that term to the one-radius expression
  `(6*r^2 + (r/2 + 3*r^2)*u/2)/|g(y)|*(1+gamma_3)` when
  `yAbs <= r` and `yhatAbs <= r`. The denominator-free radius wrapper
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_radius_bound_of_abs_bounds`
  uses `r <= 1/3` and the local lower bound `1/2 <= |g(y)|` to replace that
  tail by `2*(6*r^2 + (r/2 + 3*r^2)*u/2)*(1+gamma_3)`. The `u`-radius wrapper
  is preceded by the source-shaped rounded-exponential radius bridge
  `expm1Algorithm2_yhat_sub_one_abs_le_of_y_radius` and
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_perturb_radius_bound`:
  from `|y-1| <= r` and `|delta| <= u`, Lean derives
  `|y*(1+delta)-1| <= r + (1+r)u` and feeds that combined radius directly into
  the `3.5u` theorem. The source-domain wrapper
  `expm1Algorithm2_exp_sub_one_abs_le_of_abs_x_le`,
  `expm1LogRatio_exp_ne_zero_of_ne_zero`, and
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_x_radius_bound`
  now instantiate this local radius with `y = exp x`: `|x| <= X` gives
  `|exp x - 1| <= exp X - 1`, so the combined rounded-exponential radius is
  `(exp X - 1) + exp X*u`. The scalar adapter
  `expm1Algorithm2_exp_x_combined_radius_le_third_of_exp_mul_one_add_u_le`
  and source-domain wrapper
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_x_mul_one_add_u_bound`
  close the local smallness side condition from the compact hypothesis
  `exp X*(1+u) <= 4/3`. The `u`-radius wrapper
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_u_radius_bound_of_abs_bounds`
  specializes this to the explicit second-order tail
  `((25/2)*u^2 + 3*u^3)*(1+gamma_3)` when `yAbs <= u` and `yhatAbs <= u`.
  The direct unit-bound wrapper
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_u_radius_bound_of_unit_bounds`
  consumes the actual local inequalities `|y-1| <= u`, `|yhat-1| <= u`, and
  `|delta| <= u` directly, so future instantiations do not enumerate
  auxiliary radius cases. The named wrapper
  `expm1Algorithm2ThreePointFiveUnitBound` packages the resulting bulky
  unit-radius right-hand side as one reusable local bound. The scalar envelope
  `expm1Algorithm2ThreePointFiveUnitBoundScalar`, the equality theorem
  `expm1Algorithm2ThreePointFiveUnitBound_eq_scalar`, and
  `expm1Algorithm2ThreePointFiveUnitBoundScalar_isBigO` now expose the same
  expression as a function of `u` and prove it is `O(u)` as `u -> 0`; with
  `expm1Algorithm2ThreePointFiveUnitBound_eq_zero_of_u_eq_zero` proving the
  sanity check that the bound vanishes when `u = 0`, and
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_unit_bound_of_unit_bounds`
  exposing the compact theorem surface. The source-shaped exp-perturbation bridge is usually
  the more faithful next step when `|yhat-1|` is derived from `|y-1|` and the
  exp relative-error term rather than assumed separately. The remaining
  implementation-facing obligations are concrete exp/log routine contracts,
  Ferguson-condition verification for the actual rounded `yhat`, and the
  machine-specific Table 1.2 derivation.
  The normalized wrapper
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_normalized_remainder_of_abs_bounds`
  lets future interval or machine instantiations replace that term by
  `rem*(1+gamma_3)` from a single normalized certificate `S <= rem*|g(y)|`.
- a primitive Section 1.14.1 drift-certificate bridge:
  `expm1Algorithm2PrimitiveDriftBound`,
  `expm1Algorithm2PrimitiveSlowRemainderBound`,
  `expm1Algorithm2SlowRatioPerturbationBound_le_of_abs_bounds`,
  `expm1Algorithm2LocalDrift_le_primitive_bound`,
  `expm1Algorithm2PrimitiveSlowRemainderBound_le_of_radius`, and
  `expm1Algorithm2PrimitiveDriftBound_le_half_u_mul_abs_logRatio_add_slow_remainder`,
  `expm1Algorithm2RoundedCore_relError_le_eta_add_gamma4_of_primitive_bounds`
  reduce future interval or machine-specific Algorithm 2 instantiations to one
  elementary absolute-value budget rather than a pointwise case split.
- the Section 1.14.1 removable-singularity substrate for the slow ratio itself:
  `expm1LogRatio_tendsto_one` proves that `g(y)=(y-1)/log(y)` tends to `1` as
  `y` tends to `1` through `y != 1`.
- the Section 1.14.1 page-24 denominator expansion for the slow ratio:
  `expm1Log_one_add_sub_linear_quadratic_abs_le`,
  `expm1LogRatioDenRemainder_abs_le`, and
  `expm1LogRatio_one_add_eq_inv_one_sub_half_add_remainder` prove the explicit
  Taylor bound `log(1+v)=v-v^2/2+O(v^3)` and the exact reciprocal form
  `g(1+v)=1/(1-v/2+R(v))` with `R(v)=O(v^2)` under `|v|<1`, `v != 0`.
- the Section 1.14.1 page-24 slow-ratio expansion:
  `expm1LogRatio_one_add_sub_one_add_half_abs_le` proves the quantitative
  punctured-neighborhood bound `|g(1+v)-(1+v/2)| <= 3|v|^2` for
  `|v| <= 1/2`, `v != 0`; `expm1LogRatio_sub_one_abs_le` and
  `expm1LogRatio_self_sub_abs_le` package the corresponding quantitative
  closeness of `g(y)` to `1` and to `y`; and
  `expm1LogRatio_abs_ge_one_sub_radius_bound` plus
  `expm1LogRatio_abs_ge_half_of_radius` turn this closeness into denominator
  lower bounds for local radius proofs.
- the Section 1.14.1 two-point slow-ratio comparison:
  `expm1LogRatio_one_add_diff_sub_half_abs_le` proves
  `g(1+w)-g(1+v)=(w-v)/2+O(w^2+v^2)` quantitatively for
  `|v|, |w| <= 1/2`, `v,w != 0`.
- the Section 1.14.1 rounded-exponential substitution substrate:
  `expm1LogRatio_mul_one_add_delta_diff_sub_y_delta_half_abs_le` substitutes
  `yhat=y*(1+delta)` and proves the corresponding comparison to `y*delta/2`;
  `expm1LogRatio_mul_one_add_delta_diff_sub_delta_half_abs_le` then replaces
  `y*delta/2` by `delta/2` with the exact extra term
  `|y-1|*|delta|/2`; and
  `expm1LogRatio_mul_one_add_delta_diff_sub_logRatio_delta_half_abs_le`
  packages the comparison to `g(y)*delta/2`.
- the Section 1.14.2 exact embedded Givens block, ratio zeroing algebra, and
  rectangular zeroing schedule count: the displayed
  `[[cos theta, sin theta], [-sin theta, cos theta]]` rotation is orthogonal
  when placed in any two distinct coordinates, the affected-component formulas
  are proved exactly, the ratio choice `c=a/r`, `s=b/r` zeroes the selected
  second component, the doubled integer schedule identity matches
  `p = n*(m-(n+1)/2)`, and the Figure 1.5 `10 x 6` case has `39` rotations.
- the Section 1.15 exact power-method example core, proving that the displayed
  characteristic determinant has roots `0` and `4/5 ± sqrt(13)/10` with the
  two nonzero roots matching the displayed decimals to the shown precision, and
  that the displayed
  matrix annihilates the displayed start vector `[1,1,1]^T` in one exact
  multiplication because the start vector is a zero-eigenvalue right
  eigenvector, and that a stored perturbation `A+DeltaA` makes the first step
  exactly `DeltaA*[1,1,1]^T`.
- the Section 1.16 exact upper-Hessenberg example core, proving the displayed
  matrix shape, exact right-hand side `A*e`, exact inverse and infinity-norm
  condition-number product for `alpha=10^-7`, exact no-pivot diagonal product
  `2*(alpha+1)`, the entrywise nearby-matrix adapter and `gamma_3` entrywise
  perturbation bound for the displayed diagonal/subdiagonal perturbations,
  actual matrix determinant preservation
  through the no-pivot row eliminations, the determinant-product
  mixed-stability bridge when the diagonal product equals the exact
  determinant, the source-value determinant `10000001/5000000`, the exact
  Table 1.3 determinant/solution baseline, the printed Table 1.3 solution
  relative-error, determinant-accuracy, residual/scaled-residual contrast,
  and first multiplier `10^7`.
- the Section 1.17 exact nonrandom-rounding setup, defining Kahan's displayed
  Horner-form rational function and the `1.606 + (k-1)2^-52` grid, proving
  the sampled interval width and denominator positivity, bounding every exact
  source-interval reference value within `10^-12` of the first value, bounding
  any two exact source-grid reference values within `2*10^-12`, and bounding
  the exact reference-function endpoint variation by `10^-12`; plus the
  abstract `FPModel` rounded-Horner numerator/denominator/quotient operation
  trace with explicit local relative-error factors and the conditional
  IEEE-double finite round-to-even operation-order adapter under explicit
  finite-normal primitive-result certificates.

New Lean surface:

- `forwardErrorBounded`, `forwardErrorBoundedVec`
- `normwiseBackwardErrorBoundedVec`
- `normwiseConditionNumberBoundedVec`
- `normwiseConditionNumberSupremumVec`
- `normwiseConditionNumberAttainedVec`
- `normwiseConditionNumberSupremumVec.bounded`
- `normwiseConditionNumberSupremumVec.le_of_bound`
- `normwiseConditionNumberSupremumVec_of_attained_bound`
- `normwise_forward_from_backward_vec`
- `normwise_forward_from_backward_vec_of_condition_supremum`
- `mixedForwardBackwardErrorBounded`, `mixedForwardBackwardErrorBoundedVec`
- `mixedForwardBackward_of_backward`
- `isNumericallyStable`, `isVectorNumericallyStable`
- `isForwardStableRelativeTo`, `isVectorForwardStableRelativeTo`
- `relErrorComputedDenom`
- `relErrorComputedDenom_eq_relError_swap`
- `relErrorComputedDenom_lower_bound_from_relError`
- `relErrorComputedDenom_upper_bound_from_relError`
- `relError_lower_bound_from_computedDenom`
- `relError_upper_bound_from_computedDenom`
- `problem_1_1_relError_bounds`
- `problem12NearInteger`, `problem12CandidateInteger`
- `problem12CandidateBelow`, `problem12TableConsistent`
- `problem_1_2_candidateBelow_consistent`
- `problem_1_2_candidateBelow_between`
- `problem_1_2_candidateBelow_integer_part_last_digit_three`
- `problem_1_2_candidateInteger_consistent`
- `problem_1_2_candidateInteger_last_digit_four`
- `problem_1_2_table_does_not_force_last_digit_four`
- `problem_1_3_sqrt_one_add_sub_one`
- `problem_1_3_sin_sub_sin`
- `problem_1_3_sq_sub_sq`
- `problem_1_3_one_sub_cos_div_sin`
- `problem_1_3_lawOfCosines_radicand_sub_rewrite`
- `problem_1_3_lawOfCosines_radicand_halfAngle`
- `problem_1_3_lawOfCosines_sqrt_halfAngle`
- `complexSqrtRadius`, `complexSqrtImagSign`
- `complexSqrtStableXNonnegA`, `complexSqrtStableYNonnegA`
- `complexSqrtStableYNegA`, `complexSqrtStableXNegA`
- `complexFromRealImag`
- `complexFromRealImag_sq_eq_of_components`
- `complexSqrtStable_nonnegA_components`
- `complexSqrtStable_nonnegA_sq`
- `complexSqrtStable_negA_components`
- `complexSqrtStable_negA_sq`
- `complexSqrtStable_zero_sq`
- `CalculatorGlyph`, `invertedCalculatorDigit`
- `calculatorInvertDigits`
- `problem_1_6_07734_hello`
- `problem_1_6_38079_globe`
- `problem_1_6_318808_bobbie`
- `problem_1_6_35007_loose`
- `problem_1_6_5773857734_hells_bells`
- `problem_1_6_3331_ieee`
- `problem_1_6_5607_logs`
- `problem_1_6_5607_sq`
- `problem_1_6_real_sqrt_31438449_eq_5607`
- `subtract_perturbed_error_eq`
- `abs_subtract_perturbed_error_le`
- `abs_subtract_perturbed_error_le_eps`
- `relError_subtract_perturbed_le_eps_amp`
- `one_sub_cos_eq_two_sin_sq_half`, `one_sub_cos_nonneg_exact`
- `trigCancellationExactScaled`, `trigCancellationDirectScaledFromCos`
- `trigCancellationRewriteScaledFromSinHalf`
- `trigCancellationExactScaled_nonneg`
- `trigCancellationExactScaled_le_half`
- `trigCancellationExactScaled_lt_half`
- `trigCancellationExactScaled_pos_of_cos_ne_one`
- `trigCancellationDirectScaledFromCos_abs_error_le`
- `sq_abs_error_le_of_abs_sub_le`
- `trigCancellationRewriteScaledFromSinHalf_abs_error_le`
- `trigCancellationRewriteScaledFromSinHalf_abs_error_le_direct_cos_bound`
- `trigCancellationFiniteRoundToEvenCos`
- `trigCancellationFiniteRoundToEvenSinHalf`
- `trigCancellationDirectScaledFiniteRoundToEvenCos`
- `trigCancellationRewriteScaledFiniteRoundToEvenSinHalf`
- `trigCancellationFiniteRoundToEvenCos_abs_error_le`
- `trigCancellationFiniteRoundToEvenSinHalf_abs_error_le`
- `trigCancellationDirectScaledFiniteRoundToEvenCos_abs_error_le`
- `trigCancellationRewriteScaledFiniteRoundToEvenSinHalf_abs_error_le`
- `trigCancellationRewriteScaledFiniteRoundToEvenSinHalf_abs_error_le_direct_cos_bound`
- `trigCancellationExampleX`, `trigCancellationExampleCos10`
- `trigCancellationExampleSinHalf10`
- `trigCancellationDirectScaled`, `trigCancellationRewriteScaled`
- `trigCancellationDirectScaled_eq`
- `trigCancellationDirectScaled_ne_half`
- `trigCancellationRewriteScaled_eq_half`
- `residualRankOnePerturbation`
- `residualRankOnePerturbation_mul_vec`
- `residualRankOnePerturbation_solves`
- `frobNorm_residualRankOnePerturbation`
- `opNorm2Le_residualRankOnePerturbation`
- `residualVec_eq_matMulVec_of_perturbed_solve`
- `residual_norm_le_frobNorm_mul_solution_norm_of_perturbed_solve`
- `residual_norm_div_solution_norm_le_of_opNorm2Le_perturbed_solve`
- `relativeResidual2`
- `residualVec_add_error_eq_neg_matMulVec`
- `residual_norm_add_error_eq_matMulVec_norm`
- `roundedExactSolution_residual_norm_le_opNorm2`
- `roundedExactSolution_residual_norm_le_opNorm2_mul_relative_error`
- `roundedExactSolution_relativeResidual2_le_uncancelled`
- `roundedExactSolution_relativeResidual2_le_relative_error_factor`
- `matrixOnlyBackwardError2Le`
- `relativeMatrixOnlyBackwardError2Le`
- `higham_lemma_1_1_operator2_predicate`
- `higham_lemma_1_1_relativeResidual2_predicate`
- `relativeResidual2_le_of_relativeMatrixOnlyBackwardError2Le`
- `opNorm2Le_of_sqrt_two_infNorm_le`
- `quadraticEval`, `quadraticDiscriminant`, `flQuadraticDiscriminant`
- `flQuadraticDiscriminantAbsErrorBound`
- `flQuadraticRoundedDiscriminantSqrtInputErrorBound`
- `flQuadraticMixedDiscriminantSqrtInputErrorBound`
- `flQuadraticRoundedDiscriminantSqrtRootPlusAbsErrorBound`
- `flQuadraticRoundedDiscriminantSqrtRootMinusAbsErrorBound`
- `flQuadraticMixedDiscriminantSqrtRootPlusAbsErrorBound`
- `flQuadraticMixedDiscriminantSqrtRootMinusAbsErrorBound`
- `flQuadraticRootLargeByBSignRoundedDiscriminantSqrt`
- `flQuadraticRootSmallByBSignRoundedDiscriminantSqrt`
- `flQuadraticRootsByBSignRoundedDiscriminantSqrt`
- `flQuadraticRoundedDiscriminantSqrtRootLargeAbsErrorBound`
- `flQuadraticRoundedDiscriminantSqrtRootSmallRecoveryAbsErrorBound`
- `quadraticRootPlus`, `quadraticRootMinus`
- `quadraticRootPlusNumerator`, `quadraticRootMinusNumerator`
- `quadraticRootLargeByBSign`, `quadraticRootSmallByBSign`
- `quadraticRootMidpoint`
- `flQuadraticRecoveredRootFromOther`
- `flQuadraticRootPlusFromSqrt`, `flQuadraticRootMinusFromSqrt`
- `flQuadraticRootPlusComputedSqrt`, `flQuadraticRootMinusComputedSqrt`
- `flQuadraticRootPlusRoundedDiscriminantSqrt`
- `flQuadraticRootMinusRoundedDiscriminantSqrt`
- `flQuadraticRootPlusMixedDiscriminantSqrt`
- `flQuadraticRootMinusMixedDiscriminantSqrt`
- `quadraticRootPlus_is_root`, `quadraticRootMinus_is_root`
- `quadratic_roots_sum`, `quadratic_roots_product`
- `quadraticRootPlus_sub_midpoint_abs_eq`
- `quadraticRootMinus_sub_midpoint_abs_eq`
- `quadraticRootSeparation_abs_eq`
- `quadraticRoots_near_midpoint_of_discriminant_le`
- `quadraticRoots_near_midpoint_of_discriminant_guard_failure`
- `quadraticRootMinus_eq_c_div_a_mul_rootPlus`
- `quadraticRootPlus_eq_c_div_a_mul_rootMinus`
- `quadraticRootMinusNumerator_abs_eq_abs_b_add_s_of_b_nonneg`
- `quadraticRootPlusNumerator_abs_eq_abs_b_add_s_of_b_nonpos`
- `quadraticRootPlusNumerator_abs_le_of_b_nonneg_s_close`
- `quadraticRootMinusNumerator_abs_le_of_b_nonpos_s_close`
- `quadraticRootPlus_abs_le_rootMinus_of_b_nonneg`
- `quadraticRootMinus_abs_le_rootPlus_of_b_nonpos`
- `quadraticRootSmallByBSign_abs_le_largeByBSign`
- `flQuadraticDiscriminant_expansion`
- `flQuadraticDiscriminant_abs_error_le`
- `flQuadraticDiscriminantAbsErrorBound_nonneg`
- `flQuadraticDiscriminantAbsErrorBound_eq_poly`
- `flQuadraticDiscriminantAbsErrorBound_le_of_u_le`
- `flQuadraticDiscriminantAbsErrorBound_le_of_simulatesHigherPrecision`
- `flQuadraticDiscriminant_abs_error_le_bound`
- `flQuadraticDiscriminant_nonneg_of_abs_error_bound_le`
- `flRoundedQuotient_rel_error_le_gamma3`
- `flQuadraticRootPlusFromSqrt_rel_error_le_gamma3`
- `flQuadraticRootMinusFromSqrt_rel_error_le_gamma3`
- `quadraticRootPlus_sqrt_perturb_eq`
- `quadraticRootMinus_sqrt_perturb_eq`
- `quadraticRootPlus_sqrt_perturb_abs_le_of_abs_eps_le`
- `quadraticRootMinus_sqrt_perturb_abs_le_of_abs_eps_le`
- `quadraticRootPlus_sqrt_abs_perturb_eq`
- `quadraticRootMinus_sqrt_abs_perturb_eq`
- `quadraticRootPlus_sqrt_abs_perturb_abs_le_of_abs_sub_le`
- `quadraticRootMinus_sqrt_abs_perturb_abs_le_of_abs_sub_le`
- `flQuadraticRootPlusWithSqrtRelError_abs_error_le`
- `flQuadraticRootMinusWithSqrtRelError_abs_error_le`
- `flQuadraticRootPlusFromSqrt_abs_input_error_le`
- `flQuadraticRootMinusFromSqrt_abs_input_error_le`
- `abs_sqrt_sub_sqrt_le_sqrt_abs_sub`
- `quadraticSqrt_abs_error_le_of_discriminant_abs_error`
- `flQuadraticRootPlusFromSqrt_discriminant_abs_error_le`
- `flQuadraticRootMinusFromSqrt_discriminant_abs_error_le`
- `flQuadraticRootPlusRoundedDiscriminantSqrt_abs_error_le`
- `flQuadraticRootMinusRoundedDiscriminantSqrt_abs_error_le`
- `flQuadraticRootPlusMixedDiscriminantSqrt_abs_error_le`
- `flQuadraticRootMinusMixedDiscriminantSqrt_abs_error_le`
- `flQuadraticRootPlusComputedSqrt_abs_error_le`
- `flQuadraticRootMinusComputedSqrt_abs_error_le`
- `flQuadraticRecoveredRootFromOther_rel_error_le_gamma2`
- `flQuadraticRecoveredRootFromOther_abs_error_le_of_abs_error`
- `flQuadraticRecoveredRootMinusFromPlus_abs_error_le`
- `flQuadraticRecoveredRootPlusFromMinus_abs_error_le`
- `flQuadraticRecoveredRootMinusFromRoundedPlusDiscriminantSqrt_abs_error_le`
- `flQuadraticRecoveredRootPlusFromRoundedMinusDiscriminantSqrt_abs_error_le`
- `flQuadraticRootLargeByBSignRoundedDiscriminantSqrt_abs_error_le`
- `flQuadraticRootSmallByBSignRoundedDiscriminantSqrt_abs_error_le`
- `flQuadraticRootsByBSignRoundedDiscriminantSqrt_abs_error_le`
- `quadraticOverflowScale`
- `quadraticOverflowExample_b_square_single_finiteOverflowRange`
- `quadraticOverflowExample_b_square_double_finiteNormalRange`
- `quadraticOverflowExample_four_a_double_finiteNormalRange`
- `quadraticOverflowExample_four_ac_double_finiteNormalRange`
- `quadraticOverflowExample_discriminant_double_finiteNormalRange`
- `quadraticOverflowExample_discriminant_path_double_finiteNormalRange`
- `quadraticOverflowExample_b_square_double_roundToEvenOp_standardModel`
- `quadraticOverflowExample_four_a_double_roundToEvenOp_standardModel`
- `quadraticOverflowExample_four_ac_double_roundToEvenOp_standardModel`
- `quadraticOverflowExample_discriminant_sub_double_roundToEvenOp_standardModel`
- `FloatingPointFormat.finiteNormalRange_not_finiteUnderflowRange`
- `FloatingPointFormat.finiteNormalRange_not_finiteOverflowRange`
- `FloatingPointFormat.ieeeRoundToNearestEvenOpResult_eq_finiteNoFlags_of_finiteNormalRange`
- `FloatingPointFormat.ieeeRoundToNearestEvenOpResult_noFlags_of_finiteNormalRange`
- `FloatingPointFormat.ieeeRoundToNearestEvenOpResult_toReal?_of_finiteNormalRange`
- `FloatingPointFormat.ieeeRoundToModeOpResult_eq_finiteNoFlags_of_finiteNormalRange`
- `FloatingPointFormat.ieeeRoundToModeOpResult_noFlags_of_finiteNormalRange`
- `FloatingPointFormat.ieeeRoundToModeOpResult_toReal?_of_finiteNormalRange`
- `FloatingPointFormat.ieeeRoundToNearestEvenSqrtResult_eq_finiteNoFlags_of_finiteNormalRange`
- `FloatingPointFormat.ieeeRoundToNearestEvenSqrtResult_noFlags_of_finiteNormalRange`
- `FloatingPointFormat.ieeeRoundToNearestEvenSqrtResult_toReal?_of_finiteNormalRange`
- `FloatingPointFormat.ieeeRoundToModeSqrtResult_eq_finiteNoFlags_of_finiteNormalRange`
- `FloatingPointFormat.ieeeRoundToModeSqrtResult_noFlags_of_finiteNormalRange`
- `FloatingPointFormat.ieeeRoundToModeSqrtResult_toReal?_of_finiteNormalRange`
- `quadraticOverflowExample_b_square_double_ieeeRoundToNearestEvenOpResult_noFlags`
- `quadraticOverflowExample_four_a_double_ieeeRoundToNearestEvenOpResult_noFlags`
- `quadraticOverflowExample_four_ac_double_ieeeRoundToNearestEvenOpResult_noFlags`
- `quadraticOverflowExample_discriminant_sub_double_ieeeRoundToNearestEvenOpResult_noFlags`
- `quadraticOverflowExample_exact_discriminant_path_double_ieeeRoundToNearestEvenOpResult_noFlags`
- `quadraticOverflowExample_b_square_doubleRounded`
- `quadraticOverflowExample_four_a_doubleRounded`
- `quadraticOverflowExample_four_ac_doubleRounded`
- `quadraticOverflowExample_discriminant_doubleRounded`
- `quadraticOverflowExample_four_ac_doubleRounded_finiteNormalRange`
- `quadraticOverflowExample_discriminant_sub_doubleRounded_finiteNormalRange`
- `quadraticOverflowExample_discriminant_path_doubleRounded_finiteNormalRange`
- `quadraticOverflowExample_four_ac_doubleRounded_roundToEvenOp_standardModel`
- `quadraticOverflowExample_discriminant_sub_doubleRounded_roundToEvenOp_standardModel`
- `quadraticOverflowExample_discriminant_path_doubleRounded_roundToEvenOp_standardModel`
- `quadraticOverflowExample_four_ac_doubleRounded_ieeeRoundToNearestEvenOpResult_noFlags`
- `quadraticOverflowExample_discriminant_sub_doubleRounded_ieeeRoundToNearestEvenOpResult_noFlags`
- `quadraticOverflowExample_discriminant_path_doubleRounded_ieeeRoundToNearestEvenOpResult_noFlags`
- `quadraticOverflowExample_discriminant_path_doubleRounded_ieeeRoundToNearestEvenOpResult_toReal`
- `quadraticOverflowExample_singleOverflow_doubleRoundedDiscriminantTrace`
- `quadraticOverflowExample_scaled_b_square_single_finiteNormalRange`
- `quadraticOverflowExample_scaled_four_ac_single_finiteNormalRange`
- `quadraticOverflowExample_scaled_discriminant_single_finiteNormalRange`
- `quadraticOverflowExample_roots`
- `quadraticScaledOverflowExample_roots`
- `quadraticScaledOverflowExample_variable_scaling`
- `mullerY`, `mullerExact`, `mullerExactLimitForm`
- `mullerExact_initial0`, `mullerExact_initial1`
- `mullerExact_satisfies_recurrence`
- `mullerExact_lt_succ`, `mullerExact_lt_six`
- `mullerExact_tendsto_six`
- `problem_1_8_x34_rounds_to_5_998`
- `mullerRecurrenceStep`
- `mullerDecimal4Trace`
- `mullerDecimal4StepRoundsTo`
- `mullerDecimal4Trace_rounding_intervals`
- `mullerDecimal4Trace_34_eq_100`
- `mullerDecimal4Trace_34_abs_error_gt_94`
- `mullerModeY`, `mullerModeRatio`
- `mullerModeY_linear_recurrence`
- `mullerModeRatio_eq_hundred_sub`
- `mullerModeRatio_gt_99_of_dominant`
- `mullerModeRatio_lt_100_of_nonneg`
- `mullerModeY_dominates_of_one_le_of_two_le`
- `mullerModeRatio_gt_99_of_one_le_of_two_le`
- `mullerModeRatio_one_34_gt_99`
- `mullerModeRatio_one_34_lt_100`
- `mullerModeRatio_one_34_within_one_of_hundred`
- `sampleVarianceOnePassAggregates`
- `sampleVarianceOnePass_eq_fromAggregates`
- `flPrefixMeanStep`
- `prefixMeanStepExact`
- `flPrefixMeanStep_eq_exact_with_local_errors`
- `flPrefixMeanStep_abs_error_le`
- `flPrefixMeanStep_abs_error_le_prefixMean_succ`
- `prefixMeanStepExact_prefixMean_eq_succ`
- `prefixMeanStepExact_sub_prefixMeanStepExact`
- `flPrefixMeanTrajectory`
- `flPrefixMeanTrajectoryAbsErrorBudget`
- `flPrefixMeanTrajectoryAbsErrorBudget_nonneg`
- `flPrefixMeanTrajectory_abs_error_le_budget`
- `flPrefixCorrectedSumSquaresStep`
- `prefixCorrectedSumSquaresStepExact`
- `prefixCorrectedSumSquaresStepExact_prefix_eq_succ`
- `prefixCorrectedSumSquaresStepExact_abs_sub_le`
- `flPrefixCorrectedSumSquaresStep_eq_exact_with_local_errors`
- `flPrefixCorrectedSumSquaresStep_abs_error_le`
- `flPrefixCorrectedSumSquaresStep_abs_error_le_prefix_succ`
- `flPrefixCorrectedSumSquaresTrajectory`
- `flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget`
- `flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget_nonneg`
- `flPrefixCorrectedSumSquaresTrajectory_abs_error_le_budget`
- `sampleVariancePrefix`
- `flSampleVarianceUpdate`
- `flSampleVarianceUpdateAbsErrorBudget`
- `flSampleVarianceUpdateAbsErrorBudget_nonneg`
- `flSampleVarianceUpdate_abs_error_le_budget`
- `prefixMean_example_values_10000_10001_10002`
- `prefixCorrectedSumSquares_example_values_10000_10001_10002`
- `sampleVarianceUpdate_example_10000_10001_10002`
- `sampleVarianceOnePassAggregates_exact_example_10000_10001_10002`
- `sampleVarianceOnePassAggregates_cancelled_example_10000_10001_10002`
- `sampleVarianceOnePassAggregates_cancelled_relError_example_10000_10001_10002`
- `sampleVarianceOnePassAggregates_neg_of_sumSq_lt`
- `sampleVarianceOnePassAggregates_negative_example_10000_10001_10002`
- `sampleVarianceOnePassAggregates_negative_lt_zero_example_10000_10001_10002`
- `sampleVarianceOnePassAggregates_negative_absError_example_10000_10001_10002`
- `sampleVarianceOnePassAggregates_negative_relError_example_10000_10001_10002`
- `sampleVarianceOnePassIeeeSingleRoundingCertificate`
- `sampleVarianceOnePassIeeeSingle_sq1_sourceRoundToEvenEvidence`
- `sampleVarianceOnePassIeeeSingle_sq2_sourceRoundToEvenEvidence`
- `sampleVarianceOnePassIeeeSingle_sumSquare_exact_sourceRoundToEvenEvidence`
- `sampleVarianceOnePassIeeeSingle_sumSquare_sourceRoundToEvenEvidence`
- `sampleVarianceOnePassIeeeSingle_meanSquareTerm_exact_sourceRoundToEvenEvidence`
- `sampleVarianceOnePassIeeeSingle_meanSquareTerm_sourceRoundToEvenEvidence_of_sumSquare`
- `sampleVarianceOnePassIeeeSingle_sourceRoundingEvidenceCertificate`
- `sampleVarianceOnePassIeeeSingle_sq0_eq`
- `sampleVarianceOnePassIeeeSingle_sq1_eq`
- `sampleVarianceOnePassIeeeSingle_sq2_eq`
- `sampleVarianceOnePassIeeeSingle_sum01_eq`
- `sampleVarianceOnePassIeeeSingle_sum_eq`
- `sampleVarianceOnePassIeeeSingle_sumSq_eq_of_sq1_sq2`
- `sampleVarianceOnePassIeeeSingle_sumSq_eq_of_sq2`
- `sampleVarianceOnePassIeeeSingle_sumSq_eq`
- `sampleVarianceOnePassIeeeSingle_sumSquare_eq`
- `sampleVarianceOnePassIeeeSingle_meanSquareTerm_eq`
- `sampleVarianceOnePassIeeeSingleRoundingCertificate_of_sq2_eq`
- `sampleVarianceOnePassIeeeSingleRoundingCertificate_closed`
- `sampleVarianceOnePassIeeeSingleTrace_zero_of_roundingCertificate`
- `sampleVarianceOnePassIeeeSingleTrace_relError_one_of_roundingCertificate`
- `sampleVarianceOnePassIeeeSingleTrace_zero_of_sq2_eq`
- `sampleVarianceOnePassIeeeSingleTrace_relError_one_of_sq2_eq`
- `sampleVarianceOnePassIeeeSingleTrace_zero`
- `sampleVarianceOnePassIeeeSingleTrace_relError_one`
- `sampleVarianceOnePassIeeeSingleNegativeAggregate_inputs_finiteSystem`
- `sampleVarianceOnePassIeeeSingleNegativeAggregate_numerator_eq`
- `sampleVarianceOnePassIeeeSingleNegativeAggregateTrace_eq_neg_sixteen`
- `sampleVarianceOnePassIeeeSingleNegativeAggregateTrace_lt_zero`
- `sampleVarianceOnePassIeeeSingleNegativeAggregateTrace_relError`
- `sampleVarianceConditionDen`
- `sampleVarianceKappaCClosed`
- `sampleVarianceKappaNClosed`
- `sampleVarianceKappaNExpanded`
- `sampleVarianceDirectionalCoeff`
- `sampleVarianceConditionDen_eq_sum_sq_deviation`
- `sampleVariance_vecNorm2Sq_eq_conditionDen_add_mean_sq`
- `sampleMean_add_scaled`
- `sampleVarianceTwoPass_add_scaled_sub_eq`
- `sampleVarianceProblem17RelativeRemainderCoeff`
- `sampleVarianceProblem17RelativeRemainderEnvelope`
- `sampleVarianceTwoPass_relative_add_scaled_sub_linear_eq_remainder`
- `sampleVarianceProblem17RelativeRemainderEnvelope_isBigO`
- `sampleVarianceDirectionalCoeff_componentwise_le`
- `sampleVarianceDirectionalCoeff_normwise_le`
- `flSampleMean`
- `flSampleMean_backward_error`
- `flSampleMean_abs_error_le_gamma`
- `sampleVarianceTwoPassWithMean`
- `flSampleVarianceTwoPassWithMean`
- `flSampleVarianceTwoPass`
- `sampleMean_deviation_sum_eq_zero`
- `sum_sq_sub_perturbedMean_eq_sum_sq_sub_sampleMean_add`
- `sampleVarianceTwoPassWithMean_eq_twoPass_add`
- `sampleVarianceTwoPass_le_twoPassWithMean`
- `sampleVarianceTwoPassWithMean_relError_eq_quadratic`
- `sampleVarianceTwoPassWithMean_mul_one_add_relError_le`
- `exists_weightedRelativeErrorFactor_of_nonneg_sum`
- `flSquaredDeviationWithMean_eq_mul_one_add_gamma3`
- `flSampleVarianceTwoPassWithMean_eq_mul_one_add_gamma`
- `flSampleVarianceTwoPass_relError_le_gamma_add_mean_quadratic`
- `flSampleVarianceTwoPass_mean_quadratic_le_gamma_sq`
- `flSampleVarianceTwoPass_relError_le_gamma_add_gamma_sq_mean_bound`
- `flSampleVarianceTwoPassProblem110MeanQuadraticBound`
- `flSampleVarianceTwoPassProblem110Remainder`
- `flSampleVarianceTwoPassProblem110MeanQuadraticBound_nonneg`
- `flSampleVarianceTwoPassProblem110Remainder_nonneg`
- `flSampleVarianceTwoPassProblem110MeanQuadraticBound_eq_zero_of_u_eq_zero`
- `flSampleVarianceTwoPassProblem110Remainder_eq_zero_of_u_eq_zero`
- `flSampleVarianceTwoPassProblem110RemainderQuadraticBound`
- `flSampleVarianceTwoPassProblem110RemainderQuadraticCoeff`
- `flSampleVarianceTwoPassProblem110RemainderQuadraticBound_eq_coeff_mul_u_sq`
- `flSampleVarianceTwoPassProblem110RemainderQuadraticEnvelope`
- `flSampleVarianceTwoPassProblem110RemainderQuadraticEnvelope_eq_bound`
- `flSampleVarianceTwoPassProblem110RemainderQuadraticEnvelope_isBigO`
- `flSampleVarianceTwoPassProblem110Remainder_le_quadratic_bound`
- `gamma_eq_linear_plus_quadratic_remainder`
- `flSampleVarianceTwoPass_relError_le_linear_u_add_explicit_remainder`
- `flSampleVarianceTwoPass_relError_le_linear_u_add_problem110_remainder`
- `flSampleVarianceTwoPass_relError_eq_zero_of_u_eq_zero`
- `sampleVarianceKappaNClosed_eq_expanded`
- `sampleVarianceKappaCClosed_le_KappaNClosed`
- `det2x2`, `det2x2AbsTerms`
- `cramer2x2X1`, `cramer2x2X2`
- `det2x2Matrix`, `replaceCol2x2`, `cramer2x2Solution`
- `cramer2x2Numerator`, `cramer2x2NumeratorAbsTerms`
- `cramer2x2ComputedFromNumerators`
- `flCramer2x2Numerator`
- `cramerGeppExampleCramerSolution`
- `cramerGeppExampleCramerResidual`
- `cramerGeppExampleGeppSolution`
- `cramerGeppExampleGeppResidual`
- `cramerGeppExampleAccurateVector`
- `cramer2x2CondVec`, `cramer2x2CondAt`, `cramer2x2Inverse`
- `cramer2x2InvAbsRhs`, `cramer2x2ResidualCondVec`
- `cramer2x2ResidualCond`
- `cramer2x2_first_eq`, `cramer2x2_second_eq`
- `cramer2x2Solution_solves`
- `cramer2x2Inverse_isLeftInverse`, `cramer2x2Inverse_isRightInverse`
- `cramer2x2Inverse_isInverse`
- `cramerGeppExample_cramerSolution_rows`
- `cramerGeppExample_cramerResidual_rows`
- `cramerGeppExample_cramerScaledResidual_rows`
- `cramerGeppExample_geppSolution_rows`
- `cramerGeppExample_geppResidual_rows`
- `cramerGeppExample_geppScaledResidual_rows`
- `cramerGeppExample_accurateVector_rows`
- `cramerGeppExample_residual_signs`
- `cramerGeppExample_scaledResidual_signs`
- `cramerGeppExample_residual_component_gap`
- `cramerGeppExample_scaledResidual_component_gap`
- `cramerGeppExample_cramerResidual_infNorm_eq`
- `cramerGeppExample_cramerScaledResidual_infNorm_eq`
- `cramerGeppExample_geppResidual_infNorm_eq`
- `cramerGeppExample_geppScaledResidual_infNorm_eq`
- `cramerGeppExample_residual_infNorm_gap`
- `cramerGeppExample_scaledResidual_infNorm_gap`
- `cramerGeppExample_cramerResidual_vecNorm2Sq_eq`
- `cramerGeppExample_cramerScaledResidual_vecNorm2Sq_eq`
- `cramerGeppExample_geppResidual_vecNorm2Sq_eq`
- `cramerGeppExample_geppScaledResidual_vecNorm2Sq_eq`
- `cramerGeppExample_cramerSolution_vecNorm2Sq_eq`
- `cramerGeppExample_geppSolution_vecNorm2Sq_eq`
- `cramerGeppExample_scaledResidual_vecNorm2Sq_gap`
- `cramerGeppExample_printed_scaledResidual2Sq_gap`
- `cramer2x2_relative_forward_error_le_gamma_condAt_of_componentwise`
- `cramer2x2NumeratorAbsTerms_div_det_le_condVec_inverse_solution`
- `cramer2x2NumeratorAbsTerms_div_det_eq_invAbsRhs_inverse`
- `flDet2x2`, `flDet2x2_error_le_gamma3`
- `flCramer2x2Numerator_error_le_gamma3`
- `div_same_den_abs_error_le`
- `cramer2x2Solution_error_from_numerator_errors`
- `cramer2x2Solution_error_from_absTerm_numerator_bounds`
- `cramer2x2Solution_error_from_flNumerators_exact_den`
- `cramer2x2Solution_error_from_flNumerators_exact_den_invAbsRhs`
- `cramer2x2Residual_infNorm_le_gamma_residualCondVec_of_componentwise`
- `cramer2x2Residual_infNorm_from_flNumerators_exact_den_condInv`
- `cramer2x2Solution_relative_forward_error_from_flNumerators_exact_den_of_condVec_bound`
- `cramer2x2Solution_relative_forward_error_from_flNumerators_exact_den_condAt`
- `gepp2_relativeResidual2_le_wilkinson`
- `expOneApproxExactBase`, `expOneApproxRoundedBase`
- `expOneApproxTable11N`, `expOneApproxTable11Computed`
- `expOneApproxTable11RelativeError`
- `expOneApproxTable11_n_rows`, `expOneApproxTable11_computed_rows`
- `expOneApproxTable11_relativeError_rows`
- `expOneApproxTable11_tail_relativeError_strictly_increases`
- `expOneApproxTable11_last_two_relativeError_gt_one_tenth`
- `strassenLeafMulCount`, `strassenThresholdDimension`
- `strassenThresholdDimension_halve_leaf_succ`
- `strassenLeafMulCount_threshold_halving_decreases`
- `strassenThresholdHalving_same_dimension_and_decreases_count`
- `expOneApproxLogExpExact`
- `expOneApproxLogExpWithLogRelError`
- `expOneApproxLogExpRoundedOuter`
- `expOneApproxLogExpUnitRoundoffEnvelope`
- `expOneApproxBase_pos`
- `expOneApproxExactBase_pos`
- `expOneApproxExactBase_tendsto_exp_one`
- `expOneApproxRoundedBase_eq_exact_base_mul_initial_error_pow`
- `expOneApproxRoundedBase_relError_eq_initial_error_pow_abs`
- `expOneApproxLogExpExact_eq_exact_base`
- `expOneApproxLogExpWithLogRelError_eq_exact_base_mul_exp`
- `expOneApproxLogExpRoundedOuter_eq_exact_base_mul_exp_mul`
- `expOneApproxLogExp_exponentCoeff_nonneg`
- `expOneApproxLogExp_exponentCoeff_le_one`
- `expOneApproxLogExp_logRelError_exponent_abs_le`
- `real_abs_exp_sub_one_le_exp_abs_sub_one`
- `real_abs_exp_sub_one_le_of_abs_le`
- `expOneApproxLogExpRoundedOuter_relError_le_exp_mul`
- `expOneApproxLogExpRoundedOuter_relError_le_fp`
- `expOneApproxLogExpUnitRoundoffEnvelope_isBigO`
- `expOneApproxLogExpFiniteRoundToEven`
- `expOneApproxLogExpFiniteRoundToEven_exists_contract_of_finiteNormalRange`
- `expOneApproxLogExpFiniteRoundToEven_relError_le_fp_of_finiteNormalRange`
- `noPivotExampleA`, `noPivotExampleAInv`
- `noPivotRoundedL`, `noPivotRoundedU`
- `noPivotExampleFailureMatrix`
- `noPivotPartialPivotSwap`, `noPivotPartialPivotL`, `noPivotPartialPivotU`
- `noPivotPartialPivotIeeeSingleRoundedU`
- `noPivotPartialPivotRoundedU`
- `noPivotPartialPivotPrimitiveRoundedU`
- `noPivotPartialPivotSwap_bijective`
- `noPivotPartialPivotLUFactSpec`
- `noPivotPartialPivotLUBackwardError_zero`
- `noPivotPartialPivot_multiplier_abs_le_one`
- `noPivotPartialPivotU_diag_nonzero`
- `noPivotPartialPivotPrimitiveRoundedU_eq_roundedU_of_rounds`
- `noPivotPartialPivotRoundedLUBackwardError`
- `noPivotPartialPivotPrimitiveRoundedLUBackwardError_of_rounds`
- `noPivotExampleAInv_isInverse`
- `noPivotExampleA_infNorm_eq`
- `noPivotExampleAInv_infNorm_eq`
- `noPivotExample_kappaInf_eq`
- `noPivotRoundedLU_error_matrix`
- `noPivotRoundedLU_not_reproduce_A`
- `noPivotIeeeSingleSmallEpsilon`
- `noPivotIeeeSingleSmallEpsilon_finiteSystem`
- `noPivotIeeeSingle_partialPivot_div_epsilon_one_rounds_to_epsilon`
- `noPivotIeeeSingle_partialPivot_mul_epsilon_one_rounds_to_epsilon`
- `noPivotIeeeSingle_add_one_inv_epsilon_rounds_to_inv`
- `noPivotIeeeSingle_add_one_normalized_exp26_rounds_to_self`
- `noPivotIeeeSingle_add_one_inv_rounds_to_inv_of_inv_normalized_exp26`
- `noPivotIeeeSingle_add_one_normalized_rounds_to_self_of_two_lt_ulp`
- `noPivotIeeeSingle_add_one_normalized_rounds_to_self_of_exp_ge_26`
- `noPivotIeeeSingle_add_one_inv_rounds_to_inv_of_inv_normalized_exp_ge_26`
- `noPivotIeeeSingle_add_one_normalized_rounds_to_self_of_ulp_eq_two_even`
- `noPivotIeeeSingle_add_one_normalized_rounds_to_succ_of_ulp_eq_two_odd`
- `noPivotIeeeSingle_add_one_normalized_exp25_even_rounds_to_self`
- `noPivotIeeeSingle_add_one_normalized_exp25_odd_rounds_to_succ`
- `noPivotIeeeSingle_add_one_inv_rounds_to_inv_of_inv_normalized_exp25_even`
- `noPivotIeeeSingle_add_one_inv_rounds_to_succ_of_inv_normalized_exp25_odd`
- `noPivotIeeeSingle_add_one_normalized_exp25_max_rounds_to_exp26_min`
- `noPivotIeeeSingle_add_one_inv_rounds_to_exp26_min_of_inv_normalized_exp25_max`
- `noPivotIeeeSingle_add_one_normalized_rounds_to_self_of_left_rounding_cases`
- `noPivotIeeeSingle_add_one_inv_rounds_to_inv_of_inv_normalized_left_rounding_cases`
- `noPivotIeeeSingle_add_one_inv_rounds_to_inv_requires_inv_finiteSystem`
- `noPivotIeeeSingle_add_one_inv_not_rounds_to_inv_of_inv_not_finiteSystem`
- `noPivotIeeeSingle_add_one_epsilon_rounds_to_one`
- `noPivotIeeeSingle_partialPivot_sub_neg_one_epsilon_rounds_to_neg_one`
- `noPivotIeeeSingle_partialPivot_div_epsilon_one_rounds_to_epsilon_of_finiteSystem`
- `noPivotIeeeSingle_partialPivot_mul_epsilon_one_rounds_to_epsilon_of_finiteSystem`
- `noPivotIeeeSingle_add_one_epsilon_rounds_to_one_of_nonneg_le_small`
- `noPivotIeeeSingle_partialPivot_sub_neg_one_epsilon_rounds_to_neg_one_of_nonneg_le_small`
- `noPivotIeeeSingleSmallEpsilon_ne_zero`
- `noPivotIeeeSingleSmallEpsilon_error_matrix`
- `noPivotIeeeSinglePartialPivotRoundedLUBackwardError`
- `repeatedSqrt`, `repeatedSquare`
- `repeatedSqrt_nonneg`
- `repeatedSquare_repeatedSqrt_eq_self`
- `repeatedSquare_repeatedSqrt_sixty_eq_self`
- `hp48gSqrtSquareSurrogate`
- `hp48gTwelveDigitBelowOne`
- `Hp48gSqrtSquareSurrogateLaws`
- `hp48gSqrtSquareTrace`
- `hp48gSqrtSquareTrace_eq_surrogate_of_laws`
- `hp48gSqrtSquareSurrogate_of_nonneg_lt_one`
- `hp48gSqrtSquareSurrogate_of_ge_one`
- `hp48gSqrtSquareSurrogate_100_eq_one`
- `hp48gSqrtSquareSurrogate_absError_100`
- `hp48gSqrtSquareSurrogate_relError_100`
- `hp48gSqrtSquareSurrogate_absError_of_ge_one`
- `hp48gSqrtSquareSurrogate_relError_of_ge_one`
- `hp48gSqrtSquareSurrogate_absError_of_nonneg_lt_one`
- `hp48gSqrtSquareSurrogate_relError_of_pos_lt_one`
- `inverseSquareTerm`
- `inverseSquareTerm_4096_eq_two_pow_neg_24`
- `inverseSquareTerm_pos_of_pos`
- `inverseSquareTerm_le_4096_of_ge`
- `inverseSquareTerm_le_two_pow_neg_24_of_ge`
- `inverseSquareTerm_between_half_ulp_and_one_ulp_of_ge_2897_lt_4096`
- `inverseSquareSingleSixBeforePlateauAccumulator`
- `inverseSquareSingleFiveBeforePlateauAccumulator`
- `inverseSquareSingleFourBeforePlateauAccumulator`
- `inverseSquareSingleThreeBeforePlateauAccumulator`
- `inverseSquareSingleTwoBeforePlateauAccumulator`
- `inverseSquareSinglePrePlateauAccumulator`
- `inverseSquareSinglePlateauAccumulator`
- `inverseSquareSingleSixBeforePlateauAccumulator_lt_fiveBeforePlateau`
- `inverseSquareSingleFiveBeforePlateauAccumulator_lt_fourBeforePlateau`
- `inverseSquareSingleFourBeforePlateauAccumulator_lt_threeBeforePlateau`
- `inverseSquareSingleThreeBeforePlateauAccumulator_lt_twoBeforePlateau`
- `inverseSquareSingleTwoBeforePlateauAccumulator_lt_prePlateau`
- `inverseSquareSinglePrePlateauAccumulator_lt_plateau`
- `inverseSquareSingle_add_term_rounds_to_next_of_half_ulp_lt`
- `inverseSquareSingle_add_term_rounds_to_next_of_index_range`
- `inverseSquareSinglePrePlateauWindowStartAccumulator`
- `inverseSquareSingleForwardStep`
- `inverseSquareSingleForwardAccumulatorFrom`
- `inverseSquareSingleForwardAccumulator`
- `inverseSquareSingleForwardAccumulatorFrom_succ`
- `inverseSquareSingleForwardAccumulatorFrom_add`
- `inverseSquareSingleForwardAccumulator_add`
- `inverseSquareSingleReverseAccumulatorFrom`
- `inverseSquareSingleReverseAccumulator`
- `inverseSquareSingleReverseAccumulatorFrom_succ`
- `inverseSquareSingleReverseAccumulatorFrom_add`
- `inverseSquareSingleReverseAccumulatorFrom_finiteSystem_of_start`
- `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq`
- `inverseSquareSingleReverseAccumulator_split`
- `inverseSquareSingleReverseAccumulator_ten_pow_nine_split_4096`
- `inverseSquareReverseTenPowNineHighPrefix_index_ge_4097`
- `inverseSquareReverseTenPowNineHighPrefix_index_ge_8192`
- `inverseSquareTerm_ten_pow_nine_le_of_pos_le`
- `inverseSquareTerm_ten_pow_nine_ge_ieeeSingle_minNormal`
- `inverseSquareTerm_ge_ieeeSingle_minNormal_of_pos_le_ten_pow_nine`
- `inverseSquareTerm_le_two_pow_neg_24_of_reverse_ten_pow_nine_high_prefix`
- `inverseSquareTerm_le_two_pow_neg_26_of_ge_8192`
- `inverseSquareTerm_le_two_pow_neg_26_of_reverse_ten_pow_nine_high_binade`
- `inverseSquareExactReverseAccumulatorFrom`
- `inverseSquareExactReverseAccumulator`
- `inverseSquareExactReverseAccumulatorFrom_add_start`
- `inverseSquareExactReverseAccumulatorFrom_add`
- `inverseSquareExactReverseAccumulator_split`
- `inverseSquareExactReverseAccumulator_ten_pow_nine_split_4096`
- `inverseSquareExactReverseAccumulator_ten_pow_nine_eq_highPrefix_add_low4096`
- `inverseSquareTerm_nonneg`
- `inverseSquareTerm_le_telescope`
- `inverseSquareTerm_ge_telescope_succ`
- `inverseSquareExactReverseAccumulatorFrom_le_telescope`
- `inverseSquareExactReverseAccumulatorFrom_ge_telescope_succ`
- `inverseSquareExactReverseTenPowNineHighPrefix_le_inv_4096`
- `inverseSquareExactReverseAccumulator_ten_pow_nine_sub_low4096_le_inv_4096`
- `inverseSquareSingleReversePrintedAccumulator`
- `inverseSquareSingleReverseSuffixStartLower`
- `inverseSquareSingleReverseSuffixStartUpper`
- `inverseSquareSingleReverseSuffixStartUpperTight`
- `inverseSquareExactReverseTenPowNineHighPrefix_ge_printedSuffixStartLower`
- `inverseSquareExactReverseTenPowNineHighPrefix_le_printedSuffixStartUpper`
- `inverseSquareExactReverseTenPowNineHighPrefix_le_printedSuffixStartUpperTight`
- `inverseSquareExactReverseTenPowNineHighPrefix_mem_printedSuffixStartWindow`
- `inverseSquareExactReverseTenPowNineHighPrefix_mem_printedSuffixStartTightWindow`
- `inverseSquareExactReverseAccumulator_ten_pow_nine_sub_low4096_mem_printedSuffixStartWindow`
- `inverseSquareSingleReverseTenPowNineHighPrefixState`
- `inverseSquareSingleReverseTenPowNineHighPrefixState_split_8192`
- `inverseSquareExactReverseTenPowNineHighPrefix_split_8192`
- `inverseSquareExactReverseTenPowNineHighPrefixBefore8192_le_inv_8192`
- `inverseSquareSingleReverseTenPowNineHighPrefixBefore8192_le_inv_4096`
- `inverseSquareExactReverseBinade8192To4097_le_inv_8192`
- `inverseSquareSingleReverseBinade8192To4097_le_start_add_inv_4096`
- `inverseSquareSingleReverseHighPrefixBefore8192WindowLower`
- `inverseSquareSingleReverseHighPrefixBefore8192WindowUpper`
- `inverseSquareExactReverseTenPowNineHighPrefixBefore8192_mem_startWindow`
- `inverseSquareSingleReverseHighBinade8190To4097Prefix_eq`
- `inverseSquareSingleReverseHighBinade8190To4097WindowEndpointCertificateBool`
- `inverseSquareSingleReverseHighBinade8190To4097WindowEndpointCertificateBool_eq_true`
- `inverseSquareSingleReverseHighBinade8190To4097WindowEndpointCertificate`
- `inverseSquareSingleReverseHighBinadeAfter8192WindowLower`
- `inverseSquareSingleReverseHighBinadeAfter8192WindowUpper`
- `inverseSquareSingleReverseHighBinadeBefore8192Window_add_8192_term_mem_after8192Window`
- `inverseSquareSingleReverseHighBinadeBefore8192Window_round_8192_step_mem_after8192Window`
- `inverseSquareSingleReverseHighBinadeAfter8191WindowLower`
- `inverseSquareSingleReverseHighBinadeAfter8191WindowUpper`
- `inverseSquareSingleReverseHighBinadeAfter8192Window_round_8191_step_mem_after8191Window`
- `inverseSquareSingleReverseHighBinadeTailWindowLower`
- `inverseSquareSingleReverseHighBinadeTailWindowUpper`
- `inverseSquareSingleReverseHighBinadeTailWindowLower_final`
- `inverseSquareSingleReverseHighBinadeTailWindowUpper_final`
- `inverseSquareSingleReverseHighBinadeTailWindow_round_step_mem`
- `inverseSquareSingleReverseHighBinadeTailWindow_prefix_mem`
- `inverseSquareSingleReverseHighBinade8190To4097Window`
- `inverseSquareSingleReverseHighBinade8190To4097Window_closed`
- `inverseSquareSingleReverseHighBinade8192To4097WindowMapsToCandidate`
- `inverseSquareSingleReverseHighBinade8192To4097WindowMapsToCandidate_closed`
- `inverseSquareSingleReverseTenPowNineHighPrefixBefore8192InStartWindow`
- `inverseSquareSingleReverseTenPowNineHighPrefixBefore8192Candidate`
- `inverseSquareSingleReverseTenPowNineHighPrefixBefore8192Candidate_mem_startWindow`
- `inverseSquareSingleReverseTenPowNineHighPrefixBefore8192EqCandidate`
- `inverseSquareSingleReverseTenPowNineHighPrefixBefore8192InStartWindow_of_eq_candidate`
- `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_before8192StartWindow`
- `inverseSquareSingleReverseTenPowNineHighPrefixState_finiteSystem`
- `FloatingPointFormat.finiteRoundToEvenOp_add_ge_left_of_finiteSystem_of_nonneg`
- `FloatingPointFormat.finiteRoundToEvenOp_add_abs_error_le_right_of_finiteSystem_of_nonneg`
- `FloatingPointFormat.finiteRoundToEvenOp_add_le_left_add_two_mul_right_of_finiteSystem_of_nonneg`
- `inverseSquareSingleForwardStep_ge_self_of_finiteSystem`
- `inverseSquareSingleForwardStep_abs_error_le_term_of_finiteSystem`
- `inverseSquareSingleForwardStep_le_self_add_two_mul_term_of_finiteSystem`
- `inverseSquareSingleReverseAccumulatorFrom_start_le_of_finiteSystem`
- `inverseSquareSingleReverseAccumulatorFrom_le_of_le_steps`
- `inverseSquareSingleReverseAccumulatorFrom_nonneg_of_start_nonneg`
- `inverseSquareSingleReverseAccumulatorFrom_le_start_add_two_mul_exact_zero_start`
- `inverseSquareSingleReverseTenPowNineHighPrefixState_nonneg`
- `inverseSquareSingleReverseTenPowNineHighPrefixState_prefix_le_highPrefix`
- `inverseSquareSingleReverseTenPowNineHighPrefixState_le_two_mul_exact`
- `inverseSquareSingleReverseTenPowNineHighPrefixState_le_inv_2048`
- `inverseSquareSingleReverseTenPowNineHighPrefixStep_exactInput_finiteNormalRange`
- `inverseSquareSingleReverseTenPowNineHighPrefixStep_standardModel_lt`
- `inverseSquareSingleReverseTenPowNineHighPrefixStep_abs_error_lt_unitRoundoff_mul_exactInput`
- `inverseSquareSingleReverseTenPowNineHighPrefixStep_abs_error_lt_unitRoundoff_mul_coarse`
- `inverseSquareSingleReverseTenPowNineHighPrefixStepStdError`
- `inverseSquareSingleReverseTenPowNineHighPrefixStdErrorEnvelope`
- `inverseSquareSingleReverseTenPowNineHighPrefixStepStdError_nonneg`
- `inverseSquareSingleReverseTenPowNineHighPrefixStdErrorEnvelope_nonneg`
- `inverseSquareSingleReverseTenPowNineHighPrefix_abs_error_le_stdErrorEnvelope`
- `inverseSquareSingleReverseTenPowNineHighPrefixState_abs_error_le_stdErrorEnvelope`
- `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowMarginTarget_of_stdErrorEnvelope_le`
- `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget_of_stdErrorEnvelope_lt`
- `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_stdErrorEnvelope_le_candidateWindowMargin`
- `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_stdErrorEnvelope_lt_cellGuardMargin`
- `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_stdErrorEnvelope_le_candidateWindowMargin_closed`
- `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_stdErrorEnvelope_lt_cellGuardMargin_closed`
- `inverseSquareSingleReverseTenPowNineHighPrefixCandidate`
- `inverseSquareSingleReverseAfter4096Candidate`
- `inverseSquareSingleReverseAfter4095Candidate`
- `inverseSquareSingleReverseBefore2048Candidate`
- `inverseSquareSingleReverseAfter2048Candidate`
- `inverseSquareSingleReverseBefore1024Candidate`
- `inverseSquareSingleReverseAfter1024Candidate`
- `inverseSquareSingleReverseBefore512Candidate`
- `inverseSquareSingleReverseAfter512Candidate`
- `inverseSquareSingleReverseBefore256Candidate`
- `inverseSquareSingleReverseAfter256Candidate`
- `inverseSquareSingleReverseBefore128Candidate`
- `inverseSquareSingleReverseAfter128Candidate`
- `inverseSquareSingleReverseBefore64Candidate`
- `inverseSquareSingleReverseAfter64Candidate`
- `inverseSquareSingleReverseBefore32Candidate`
- `inverseSquareSingleReverseAfter32Candidate`
- `inverseSquareSingleReverseBefore16Candidate`
- `inverseSquareSingleReverseAfter16Candidate`
- `inverseSquareSingleReverseBefore8Candidate`
- `inverseSquareSingleReverseAfter8Candidate`
- `inverseSquareSingleReverseBefore4Candidate`
- `inverseSquareSingleReverseAfter4Candidate`
- `inverseSquareSingleReverseAfter3Candidate`
- `inverseSquareSingleReverseAfter2Candidate`
- `inverseSquareSingleReverseTenPowNineHighPrefixCandidate_mem_printedSuffixStartWindow`
- `inverseSquareSingleReverseTenPowNineHighPrefixCandidate_mem_printedSuffixStartTightWindow`
- `inverseSquareSingleForwardStep_eq_left_of_adjacent_strict_between_left_closer`
- `inverseSquareSingleForwardStep_eq_right_of_adjacent_strict_between_right_closer`
- `inverseSquareSingleForwardStep_normalizedValue_nearest_mantissa_of_scaled_bounds_at_scale`
- `inverseSquareSingleForwardStep_normalizedValue_eq_self_of_scaled_half_ulp_at_scale`
- `inverseSquareSingleReverseAccumulatorFrom_scaledBandPrefix_of_le`
- `inverseSquareSingleReverseCandidate_add_4096_term_rounds_to_after4096`
- `inverseSquareSingleReverseAfter4096_add_4095_term_rounds_to_after4095`
- `inverseSquareSingleReverseAfter4095Prefix_4094_to_2049_eq`
- `inverseSquareSingleReverseAfter4095Band4094To2049CertificateBool`
- `inverseSquareSingleReverseAfter4095Band4094To2049CertificateBool_eq_true`
- `inverseSquareSingleReverseAfter4095Band4094To2049Certificate`
- `inverseSquareSingleReverseAfter4095Accumulator_4094_bandPrefix_of_le`
- `inverseSquareSingleReverseAfter4095Accumulator_4094_to_before2048`
- `inverseSquareSingleReverseBefore2048_add_2048_term_rounds_to_after2048`
- `inverseSquareSingleReverseAfter2048Prefix_2047_to_1025_eq`
- `inverseSquareSingleReverseAfter2048Band2047To1025CertificateBool`
- `inverseSquareSingleReverseAfter2048Band2047To1025CertificateBool_eq_true`
- `inverseSquareSingleReverseAfter2048Band2047To1025Certificate`
- `inverseSquareSingleReverseAfter2048Accumulator_2047_bandPrefix_of_le`
- `inverseSquareSingleReverseAfter2048Accumulator_2047_to_before1024`
- `inverseSquareSingleReverseBefore1024_add_1024_term_rounds_to_after1024`
- `inverseSquareSingleReverseAfter1024Prefix_1023_to_513_eq`
- `inverseSquareSingleReverseAfter1024Band1023To513CertificateBool`
- `inverseSquareSingleReverseAfter1024Band1023To513CertificateBool_eq_true`
- `inverseSquareSingleReverseAfter1024Band1023To513Certificate`
- `inverseSquareSingleReverseAfter1024Accumulator_1023_bandPrefix_of_le`
- `inverseSquareSingleReverseAfter1024Accumulator_1023_to_before512`
- `inverseSquareSingleReverseBefore512_add_512_term_rounds_to_after512`
- `inverseSquareSingleReverseAfter512Prefix_511_to_257_eq`
- `inverseSquareSingleReverseAfter512Band511To257CertificateBool`
- `inverseSquareSingleReverseAfter512Band511To257CertificateBool_eq_true`
- `inverseSquareSingleReverseAfter512Band511To257Certificate`
- `inverseSquareSingleReverseAfter512Accumulator_511_bandPrefix_of_le`
- `inverseSquareSingleReverseAfter512Accumulator_511_to_before256`
- `inverseSquareSingleReverseBefore256_add_256_term_rounds_to_after256`
- `inverseSquareSingleReverseAfter256Prefix_255_to_129_eq`
- `inverseSquareSingleReverseAfter256Band255To129CertificateBool`
- `inverseSquareSingleReverseAfter256Band255To129CertificateBool_eq_true`
- `inverseSquareSingleReverseAfter256Band255To129Certificate`
- `inverseSquareSingleReverseAfter256Accumulator_255_bandPrefix_of_le`
- `inverseSquareSingleReverseAfter256Accumulator_255_to_before128`
- `inverseSquareSingleReverseBefore128_add_128_term_rounds_to_after128`
- `inverseSquareSingleReverseAfter128Prefix_127_to_65_eq`
- `inverseSquareSingleReverseAfter128Band127To65CertificateBool`
- `inverseSquareSingleReverseAfter128Band127To65CertificateBool_eq_true`
- `inverseSquareSingleReverseAfter128Band127To65Certificate`
- `inverseSquareSingleReverseAfter128Accumulator_127_bandPrefix_of_le`
- `inverseSquareSingleReverseAfter128Accumulator_127_to_before64`
- `inverseSquareSingleReverseBefore64_add_64_term_rounds_to_after64`
- `inverseSquareSingleReverseAfter64Prefix_63_to_33_eq`
- `inverseSquareSingleReverseAfter64Band63To33CertificateBool`
- `inverseSquareSingleReverseAfter64Band63To33CertificateBool_eq_true`
- `inverseSquareSingleReverseAfter64Band63To33Certificate`
- `inverseSquareSingleReverseAfter64Accumulator_63_bandPrefix_of_le`
- `inverseSquareSingleReverseAfter64Accumulator_63_to_before32`
- `inverseSquareSingleReverseBefore32_add_32_term_rounds_to_after32`
- `inverseSquareSingleReverseAfter32Prefix_31_to_17_eq`
- `inverseSquareSingleReverseAfter32Band31To17CertificateBool`
- `inverseSquareSingleReverseAfter32Band31To17CertificateBool_eq_true`
- `inverseSquareSingleReverseAfter32Band31To17Certificate`
- `inverseSquareSingleReverseAfter32Accumulator_31_bandPrefix_of_le`
- `inverseSquareSingleReverseAfter32Accumulator_31_to_before16`
- `inverseSquareSingleReverseBefore16_add_16_term_rounds_to_after16`
- `inverseSquareSingleReverseAfter16Prefix_15_to_9_eq`
- `inverseSquareSingleReverseAfter16Band15To9CertificateBool`
- `inverseSquareSingleReverseAfter16Band15To9CertificateBool_eq_true`
- `inverseSquareSingleReverseAfter16Band15To9Certificate`
- `inverseSquareSingleReverseAfter16Accumulator_15_bandPrefix_of_le`
- `inverseSquareSingleReverseAfter16Accumulator_15_to_before8`
- `inverseSquareSingleReverseBefore8_add_8_term_rounds_to_after8`
- `inverseSquareSingleReverseAfter8Prefix_7_to_5_eq`
- `inverseSquareSingleReverseAfter8Band7To5CertificateBool`
- `inverseSquareSingleReverseAfter8Band7To5CertificateBool_eq_true`
- `inverseSquareSingleReverseAfter8Band7To5Certificate`
- `inverseSquareSingleReverseAfter8Accumulator_7_bandPrefix_of_le`
- `inverseSquareSingleReverseAfter8Accumulator_7_to_before4`
- `inverseSquareSingleReverseBefore4_add_4_term_rounds_to_after4`
- `inverseSquareSingleReverseAfter4_add_3_term_rounds_to_after3`
- `inverseSquareSingleReverseAfter3_add_2_term_rounds_to_after2`
- `inverseSquareSingleReverseAfter2_add_1_term_rounds_to_printed`
- `inverseSquareSingleReverseTenPowNineHighPrefixEqCandidate`
- `inverseSquareSingleReverseCandidateSuffixMapsToPrinted`
- `inverseSquareSingleReverseAfter4096SuffixMapsToPrinted`
- `inverseSquareSingleReverseAfter4095SuffixMapsToPrinted`
- `inverseSquareSingleReverseBefore2048SuffixMapsToPrinted`
- `inverseSquareSingleReverseBefore1024SuffixMapsToPrinted`
- `inverseSquareSingleReverseBefore512SuffixMapsToPrinted`
- `inverseSquareSingleReverseBefore256SuffixMapsToPrinted`
- `inverseSquareSingleReverseBefore128SuffixMapsToPrinted`
- `inverseSquareSingleReverseBefore64SuffixMapsToPrinted`
- `inverseSquareSingleReverseBefore32SuffixMapsToPrinted`
- `inverseSquareSingleReverseBefore16SuffixMapsToPrinted`
- `inverseSquareSingleReverseBefore8SuffixMapsToPrinted`
- `inverseSquareSingleReverseBefore4SuffixMapsToPrinted`
- `inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixWindow`
- `inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow`
- `inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixWindow_of_eq_candidate`
- `inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow_of_eq_candidate`
- `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_candidate_certificates`
- `inverseSquareSingleReverseCandidateSuffixMapsToPrinted_of_after4096`
- `inverseSquareSingleReverseAfter4096SuffixMapsToPrinted_of_after4095`
- `inverseSquareSingleReverseAfter4095SuffixMapsToPrinted_of_before2048`
- `inverseSquareSingleReverseBefore2048SuffixMapsToPrinted_of_before1024`
- `inverseSquareSingleReverseBefore1024SuffixMapsToPrinted_of_before512`
- `inverseSquareSingleReverseBefore512SuffixMapsToPrinted_of_before256`
- `inverseSquareSingleReverseBefore256SuffixMapsToPrinted_of_before128`
- `inverseSquareSingleReverseBefore128SuffixMapsToPrinted_of_before64`
- `inverseSquareSingleReverseBefore64SuffixMapsToPrinted_of_before32`
- `inverseSquareSingleReverseBefore32SuffixMapsToPrinted_of_before16`
- `inverseSquareSingleReverseBefore16SuffixMapsToPrinted_of_before8`
- `inverseSquareSingleReverseBefore8SuffixMapsToPrinted_of_before4`
- `inverseSquareSingleReverseBefore4SuffixMapsToPrinted_closed`
- `inverseSquareSingleReverseBefore32SuffixMapsToPrinted_closed`
- `inverseSquareSingleReverseCandidateSuffixMapsToPrinted_closed`
- `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_eq_candidate`
- `inverseSquareSingleReverseSuffixWindowMapsToPrinted`
- `inverseSquareSingleReverseTightSuffixWindowMapsToPrinted`
- `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_window_certificates`
- `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_mem_window`
- `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_tight_window_certificates`
- `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_mem_tight_window`
- `inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixWindow_of_eq_exact`
- `inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow_of_eq_exact`
- `inverseSquareSingleReverseHighPrefixTightWindowMargin`
- `inverseSquareSingleReverseHighPrefixTightWindowMargin_nonneg`
- `inverseSquareSingleReverseHighPrefixTightWindowMarginLowerBound`
- `inverseSquareSingleReverseHighPrefixTightWindowMarginLowerBound_nonneg`
- `inverseSquareSingleReverseHighPrefixTightWindowMarginLowerBound_le_margin`
- `inverseSquareTerm_ge_shifted_telescope_4096_8193`
- `inverseSquareExactReverseAccumulatorFrom_ge_shifted_telescope_4096_8193`
- `inverseSquareExactReverseTenPowNineHighPrefix_ge_shifted_telescope_4096_8193`
- `inverseSquareTerm_le_half_telescope`
- `inverseSquareExactReverseAccumulatorFrom_le_half_telescope`
- `inverseSquareExactReverseTenPowNineHighPrefix_le_half_telescope`
- `inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint`
- `inverseSquareSingleReverseHighPrefixHalfUpperEndpoint`
- `inverseSquareSingleReverseHighPrefixTightWindowMarginShiftedLowerBound`
- `inverseSquareSingleReverseHighPrefixTightWindowMarginShiftedLowerBound_nonneg`
- `inverseSquareSingleReverseHighPrefixTightWindowMarginShiftedLowerBound_le_margin`
- `inverseSquareSingleReverseTenPowNineHighPrefixCandidate_abs_error_le_shiftedMarginLowerBound`
- `inverseSquareSingleReverseHighPrefixCandidateWindowLower`
- `inverseSquareSingleReverseHighPrefixCandidateWindowUpper`
- `inverseSquareSingleReverseHighPrefixCandidateWindowLowerPred`
- `inverseSquareSingleReverseHighPrefixCandidateWindowUpperSucc`
- `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow`
- `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuard`
- `inverseSquareSingleReverseTenPowNineHighPrefixCandidate_mem_candidateWindow`
- `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuard_of_eq_candidate`
- `inverseSquareExactReverseTenPowNineHighPrefix_mem_candidateWindow`
- `inverseSquareExactReverseTenPowNineHighPrefix_mem_candidateWindowCellGuard`
- `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_eq_exact`
- `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_eq_candidate`
- `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_cellGuard`
- `inverseSquareSingleReverseHighPrefixCandidateWindow_mem_printedSuffixStartTightWindow`
- `inverseSquareSingleReverseCandidateWindowMapsToPrinted`
- `inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_tightSuffixWindow`
- `inverseSquareSingleReverseAfter4096CandidateWindowLower`
- `inverseSquareSingleReverseAfter4096CandidateWindowUpper`
- `inverseSquareSingleReverseAfter4096Candidate_mem_after4096Window`
- `inverseSquareSingleReverseCandidateWindow_add_4096_term_mem_after4096Window`
- `FloatingPointFormat.nearestRoundingToFinite_mem_Icc_of_finite_endpoints`
- `inverseSquareSingleReverseCandidateWindow_round_4096_step_mem_after4096Window`
- `inverseSquareSingleReverseAfter4096WindowMapsToPrinted`
- `inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_after4096Window`
- `inverseSquareSingleReverseAfter4095CandidateWindowLower`
- `inverseSquareSingleReverseAfter4095CandidateWindowUpper`
- `inverseSquareSingleReverseAfter4095Candidate_mem_after4095Window`
- `inverseSquareSingleReverseAfter4096Window_add_4095_term_mem_after4095Window`
- `inverseSquareSingleReverseAfter4096Window_round_4095_step_mem_after4095Window`
- `inverseSquareSingleReverseAfter4095WindowMapsToPrinted`
- `inverseSquareSingleReverseAfter4096WindowMapsToPrinted_of_after4095Window`
- `inverseSquareSingleReverseBefore2048CandidateWindowLower`
- `inverseSquareSingleReverseBefore2048CandidateWindowUpper`
- `inverseSquareSingleReverseBefore2048Candidate_mem_before2048Window`
- `FloatingPointFormat.finiteSystem_lt_right_adjacent_le_left`
- `FloatingPointFormat.right_adjacent_le_finiteSystem_of_left_lt`
- `FloatingPointFormat.nearestRoundingToFinite_ge_of_adjacent_midpoint`
- `FloatingPointFormat.nearestRoundingToFinite_le_of_adjacent_midpoint`
- `abs_sub_right_lt_abs_sub_left_of_le_of_right_closer`
- `abs_sub_left_lt_abs_sub_right_of_le_of_left_closer`
- `inverseSquareSingleReverseAfter4095BandWindowLower`
- `inverseSquareSingleReverseAfter4095BandWindowUpper`
- `inverseSquareSingleReverseAfter4095BandWindowLower_zero`
- `inverseSquareSingleReverseAfter4095BandWindowUpper_zero`
- `inverseSquareSingleReverseAfter4095BandWindowLower_final`
- `inverseSquareSingleReverseAfter4095BandWindowUpper_final`
- `inverseSquareSingleReverseAfter4095Band4094To2049WindowEndpointCertificateBool`
- `inverseSquareSingleReverseAfter4095Band4094To2049WindowEndpointCertificateBool_eq_true`
- `inverseSquareSingleReverseAfter4095Band4094To2049WindowEndpointCertificate`
- `inverseSquareSingleReverseAfter4095BandWindow_round_step_mem`
- `inverseSquareSingleReverseAfter4095BandWindow_prefix_mem`
- `inverseSquareSingleReverseAfter4095WindowLower_band4094_to_before2048_eq`
- `inverseSquareSingleReverseAfter4095WindowUpper_band4094_to_before2048_eq`
- `inverseSquareSingleReverseAfter4095Band4094ToBefore2048Window`
- `inverseSquareSingleReverseAfter4095Band4094ToBefore2048Window_closed`
- `inverseSquareSingleReverseAfter4095Candidate_band4094_to_before2048_mem_before2048Window`
- `inverseSquareSingleReverseBefore2048WindowMapsToPrinted`
- `inverseSquareSingleReverseAfter2048CandidateWindowLower`
- `inverseSquareSingleReverseAfter2048CandidateWindowUpper`
- `inverseSquareSingleReverseAfter2048Candidate_mem_after2048Window`
- `inverseSquareSingleReverseBefore2048Window_add_2048_term_mem_after2048Window`
- `inverseSquareSingleReverseBefore2048Window_round_2048_step_mem_after2048Window`
- `inverseSquareSingleReverseAfter2048WindowMapsToPrinted`
- `inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_after2048Window`
- `inverseSquareSingleReverseBefore1024CandidateWindowLower`
- `inverseSquareSingleReverseBefore1024CandidateWindowUpper`
- `inverseSquareSingleReverseBefore1024Candidate_mem_before1024Window`
- `inverseSquareSingleReverseAfter2048BandWindowLower`
- `inverseSquareSingleReverseAfter2048BandWindowUpper`
- `inverseSquareSingleReverseAfter2048BandWindowLower_zero`
- `inverseSquareSingleReverseAfter2048BandWindowUpper_zero`
- `inverseSquareSingleReverseAfter2048BandWindowLower_final`
- `inverseSquareSingleReverseAfter2048BandWindowUpper_final`
- `inverseSquareSingleReverseAfter2048Band2047To1025WindowEndpointCertificateBool`
- `inverseSquareSingleReverseAfter2048Band2047To1025WindowEndpointCertificateBool_eq_true`
- `inverseSquareSingleReverseAfter2048Band2047To1025WindowEndpointCertificate`
- `inverseSquareSingleReverseAfter2048BandWindow_round_step_mem`
- `inverseSquareSingleReverseAfter2048BandWindow_prefix_mem`
- `inverseSquareSingleReverseAfter2048Band2047ToBefore1024Window`
- `inverseSquareSingleReverseAfter2048Band2047ToBefore1024Window_closed`
- `inverseSquareSingleReverseAfter2048Candidate_band2047_to_before1024_mem_before1024Window`
- `inverseSquareSingleReverseBefore1024WindowMapsToPrinted`
- `inverseSquareSingleReverseAfter2048WindowMapsToPrinted_of_band2047_to_before1024Window`
- `inverseSquareSingleReverseAfter2048WindowMapsToPrinted_of_before1024Window`
- `inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before1024Window`
- `inverseSquareSingleReverseAfter1024CandidateWindowLower`
- `inverseSquareSingleReverseAfter1024CandidateWindowUpper`
- `inverseSquareSingleReverseAfter1024Candidate_mem_after1024Window`
- `inverseSquareSingleReverseBefore1024Window_add_1024_term_mem_after1024Window`
- `inverseSquareSingleReverseBefore1024Window_round_1024_step_mem_after1024Window`
- `inverseSquareSingleReverseAfter1024WindowMapsToPrinted`
- `inverseSquareSingleReverseBefore1024WindowMapsToPrinted_of_after1024Window`
- `inverseSquareSingleReverseBefore512CandidateWindowLower`
- `inverseSquareSingleReverseBefore512CandidateWindowUpper`
- `inverseSquareSingleReverseBefore512Candidate_mem_before512Window`
- `inverseSquareSingleReverseAfter1024BandWindowLower`
- `inverseSquareSingleReverseAfter1024BandWindowUpper`
- `inverseSquareSingleReverseAfter1024BandWindowLower_zero`
- `inverseSquareSingleReverseAfter1024BandWindowUpper_zero`
- `inverseSquareSingleReverseAfter1024BandWindowLower_final`
- `inverseSquareSingleReverseAfter1024BandWindowUpper_final`
- `inverseSquareSingleReverseAfter1024Band1023To513WindowEndpointCertificateBool`
- `inverseSquareSingleReverseAfter1024Band1023To513WindowEndpointCertificateBool_eq_true`
- `inverseSquareSingleReverseAfter1024Band1023To513WindowEndpointCertificate`
- `inverseSquareSingleReverseAfter1024BandWindow_round_step_mem`
- `inverseSquareSingleReverseAfter1024BandWindow_prefix_mem`
- `inverseSquareSingleReverseAfter1024Band1023ToBefore512Window`
- `inverseSquareSingleReverseAfter1024Band1023ToBefore512Window_closed`
- `inverseSquareSingleReverseAfter1024Candidate_band1023_to_before512_mem_before512Window`
- `inverseSquareSingleReverseBefore512WindowMapsToPrinted`
- `inverseSquareSingleReverseAfter1024WindowMapsToPrinted_of_band1023_to_before512Window`
- `inverseSquareSingleReverseAfter1024WindowMapsToPrinted_of_before512Window`
- `inverseSquareSingleReverseBefore1024WindowMapsToPrinted_of_before512Window`
- `inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before512Window`
- `inverseSquareSingleReverseAfter512CandidateWindowLower`
- `inverseSquareSingleReverseAfter512CandidateWindowUpper`
- `inverseSquareSingleReverseAfter512Candidate_mem_after512Window`
- `inverseSquareSingleReverseBefore512Window_add_512_term_mem_after512Window`
- `inverseSquareSingleReverseBefore512Window_round_512_step_mem_after512Window`
- `inverseSquareSingleReverseAfter512WindowMapsToPrinted`
- `inverseSquareSingleReverseBefore512WindowMapsToPrinted_of_after512Window`
- `inverseSquareSingleReverseBefore256CandidateWindowLower`
- `inverseSquareSingleReverseBefore256CandidateWindowUpper`
- `inverseSquareSingleReverseBefore256Candidate_mem_before256Window`
- `inverseSquareSingleReverseAfter512BandWindowLower`
- `inverseSquareSingleReverseAfter512BandWindowUpper`
- `inverseSquareSingleReverseAfter512BandWindowLower_zero`
- `inverseSquareSingleReverseAfter512BandWindowUpper_zero`
- `inverseSquareSingleReverseAfter512BandWindowLower_final`
- `inverseSquareSingleReverseAfter512BandWindowUpper_final`
- `inverseSquareSingleReverseAfter512Band511To257WindowEndpointCertificateBool`
- `inverseSquareSingleReverseAfter512Band511To257WindowEndpointCertificateBool_eq_true`
- `inverseSquareSingleReverseAfter512Band511To257WindowEndpointCertificate`
- `inverseSquareSingleReverseAfter512BandWindow_round_step_mem`
- `inverseSquareSingleReverseAfter512BandWindow_prefix_mem`
- `inverseSquareSingleReverseAfter512Band511ToBefore256Window`
- `inverseSquareSingleReverseAfter512Band511ToBefore256Window_closed`
- `inverseSquareSingleReverseAfter512Candidate_band511_to_before256_mem_before256Window`
- `inverseSquareSingleReverseBefore256WindowMapsToPrinted`
- `inverseSquareSingleReverseAfter512WindowMapsToPrinted_of_band511_to_before256Window`
- `inverseSquareSingleReverseAfter512WindowMapsToPrinted_of_before256Window`
- `inverseSquareSingleReverseBefore512WindowMapsToPrinted_of_before256Window`
- `inverseSquareSingleReverseBefore1024WindowMapsToPrinted_of_before256Window`
- `inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before256Window`
- `inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_band4094_to_before2048Window`
- `inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before2048Window`
- `inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before1024Window`
- `inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before512Window`
- `inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before256Window`
- `inverseSquareSingleReverseAfter256CandidateWindowLower`
- `inverseSquareSingleReverseAfter256CandidateWindowUpper`
- `inverseSquareSingleReverseAfter256Candidate_mem_after256Window`
- `inverseSquareSingleReverseBefore256Window_add_256_term_mem_after256Window`
- `inverseSquareSingleReverseBefore256Window_round_256_step_mem_after256Window`
- `inverseSquareSingleReverseAfter256WindowMapsToPrinted`
- `inverseSquareSingleReverseBefore256WindowMapsToPrinted_of_after256Window`
- `inverseSquareSingleReverseBefore128CandidateWindowLower`
- `inverseSquareSingleReverseBefore128CandidateWindowUpper`
- `inverseSquareSingleReverseBefore128Candidate_mem_before128Window`
- `inverseSquareSingleReverseAfter256BandWindowLower`
- `inverseSquareSingleReverseAfter256BandWindowUpper`
- `inverseSquareSingleReverseAfter256BandWindowLower_zero`
- `inverseSquareSingleReverseAfter256BandWindowUpper_zero`
- `inverseSquareSingleReverseAfter256BandWindowLower_final`
- `inverseSquareSingleReverseAfter256BandWindowUpper_final`
- `inverseSquareSingleReverseAfter256Band255To129WindowEndpointCertificateBool`
- `inverseSquareSingleReverseAfter256Band255To129WindowEndpointCertificateBool_eq_true`
- `inverseSquareSingleReverseAfter256Band255To129WindowEndpointCertificate`
- `inverseSquareSingleReverseAfter256BandWindow_round_step_mem`
- `inverseSquareSingleReverseAfter256BandWindow_prefix_mem`
- `inverseSquareSingleReverseAfter256Band255ToBefore128Window`
- `inverseSquareSingleReverseAfter256Band255ToBefore128Window_closed`
- `inverseSquareSingleReverseAfter256Candidate_band255_to_before128_mem_before128Window`
- `inverseSquareSingleReverseBefore128WindowMapsToPrinted`
- `inverseSquareSingleReverseAfter256WindowMapsToPrinted_of_band255_to_before128Window`
- `inverseSquareSingleReverseAfter256WindowMapsToPrinted_of_before128Window`
- `inverseSquareSingleReverseBefore256WindowMapsToPrinted_of_before128Window`
- `inverseSquareSingleReverseBefore512WindowMapsToPrinted_of_before128Window`
- `inverseSquareSingleReverseBefore1024WindowMapsToPrinted_of_before128Window`
- `inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before128Window`
- `inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before128Window`
- `inverseSquareSingleReverseAfter128CandidateWindowLower`
- `inverseSquareSingleReverseAfter128CandidateWindowUpper`
- `inverseSquareSingleReverseAfter128Candidate_mem_after128Window`
- `inverseSquareSingleReverseBefore128Window_add_128_term_mem_after128Window`
- `inverseSquareSingleReverseBefore128Window_round_128_step_mem_after128Window`
- `inverseSquareSingleReverseAfter128WindowMapsToPrinted`
- `inverseSquareSingleReverseBefore128WindowMapsToPrinted_of_after128Window`
- `inverseSquareSingleReverseBefore64CandidateWindowLower`
- `inverseSquareSingleReverseBefore64CandidateWindowUpper`
- `inverseSquareSingleReverseBefore64Candidate_mem_before64Window`
- `inverseSquareSingleReverseAfter128BandWindowLower`
- `inverseSquareSingleReverseAfter128BandWindowUpper`
- `inverseSquareSingleReverseAfter128BandWindowLower_zero`
- `inverseSquareSingleReverseAfter128BandWindowUpper_zero`
- `inverseSquareSingleReverseAfter128BandWindowLower_final`
- `inverseSquareSingleReverseAfter128BandWindowUpper_final`
- `inverseSquareSingleReverseAfter128Band127To65WindowEndpointCertificateBool`
- `inverseSquareSingleReverseAfter128Band127To65WindowEndpointCertificateBool_eq_true`
- `inverseSquareSingleReverseAfter128Band127To65WindowEndpointCertificate`
- `inverseSquareSingleReverseAfter128BandWindow_round_step_mem`
- `inverseSquareSingleReverseAfter128BandWindow_prefix_mem`
- `inverseSquareSingleReverseAfter128Band127ToBefore64Window`
- `inverseSquareSingleReverseAfter128Band127ToBefore64Window_closed`
- `inverseSquareSingleReverseAfter128Candidate_band127_to_before64_mem_before64Window`
- `inverseSquareSingleReverseBefore64WindowMapsToPrinted`
- `inverseSquareSingleReverseAfter128WindowMapsToPrinted_of_band127_to_before64Window`
- `inverseSquareSingleReverseAfter128WindowMapsToPrinted_of_before64Window`
- `inverseSquareSingleReverseBefore128WindowMapsToPrinted_of_before64Window`
- `inverseSquareSingleReverseBefore256WindowMapsToPrinted_of_before64Window`
- `inverseSquareSingleReverseBefore512WindowMapsToPrinted_of_before64Window`
- `inverseSquareSingleReverseBefore1024WindowMapsToPrinted_of_before64Window`
- `inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before64Window`
- `inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before64Window`
- `inverseSquareSingleReverseAfter64CandidateWindowLower`
- `inverseSquareSingleReverseAfter64CandidateWindowUpper`
- `inverseSquareSingleReverseAfter64Candidate_mem_after64Window`
- `inverseSquareSingleReverseBefore64Window_add_64_term_mem_after64Window`
- `inverseSquareSingleReverseBefore64Window_round_64_step_mem_after64Window`
- `inverseSquareSingleReverseAfter64WindowMapsToPrinted`
- `inverseSquareSingleReverseBefore64WindowMapsToPrinted_of_after64Window`
- `inverseSquareSingleReverseBefore32CandidateWindowLower`
- `inverseSquareSingleReverseBefore32CandidateWindowUpper`
- `inverseSquareSingleReverseBefore32Candidate_mem_before32Window`
- `inverseSquareSingleReverseAfter64BandWindowLower`
- `inverseSquareSingleReverseAfter64BandWindowUpper`
- `inverseSquareSingleReverseAfter64BandWindowLower_zero`
- `inverseSquareSingleReverseAfter64BandWindowUpper_zero`
- `inverseSquareSingleReverseAfter64BandWindowLower_final`
- `inverseSquareSingleReverseAfter64BandWindowUpper_final`
- `inverseSquareSingleReverseAfter64Band63To33WindowEndpointCertificateBool`
- `inverseSquareSingleReverseAfter64Band63To33WindowEndpointCertificateBool_eq_true`
- `inverseSquareSingleReverseAfter64Band63To33WindowEndpointCertificate`
- `inverseSquareSingleReverseAfter64BandWindow_round_step_mem`
- `inverseSquareSingleReverseAfter64BandWindow_prefix_mem`
- `inverseSquareSingleReverseAfter64Band63ToBefore32Window`
- `inverseSquareSingleReverseAfter64Band63ToBefore32Window_closed`
- `inverseSquareSingleReverseAfter64Candidate_band63_to_before32_mem_before32Window`
- `inverseSquareSingleReverseBefore32WindowMapsToPrinted`
- `inverseSquareSingleReverseAfter64WindowMapsToPrinted_of_band63_to_before32Window`
- `inverseSquareSingleReverseAfter64WindowMapsToPrinted_of_before32Window`
- `inverseSquareSingleReverseBefore64WindowMapsToPrinted_of_before32Window`
- `inverseSquareSingleReverseBefore128WindowMapsToPrinted_of_before32Window`
- `inverseSquareSingleReverseBefore256WindowMapsToPrinted_of_before32Window`
- `inverseSquareSingleReverseBefore512WindowMapsToPrinted_of_before32Window`
- `inverseSquareSingleReverseBefore1024WindowMapsToPrinted_of_before32Window`
- `inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before32Window`
- `inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before32Window`
- `inverseSquareSingleReverseAfter32CandidateWindowLower`
- `inverseSquareSingleReverseAfter32CandidateWindowUpper`
- `inverseSquareSingleReverseAfter32Candidate_mem_after32Window`
- `inverseSquareSingleReverseBefore32Window_add_32_term_mem_after32Window`
- `inverseSquareSingleReverseBefore32Window_round_32_step_mem_after32Window`
- `inverseSquareSingleReverseAfter32WindowMapsToPrinted`
- `inverseSquareSingleReverseBefore32WindowMapsToPrinted_of_after32Window`
- `inverseSquareSingleReverseBefore16CandidateWindowLower`
- `inverseSquareSingleReverseBefore16CandidateWindowUpper`
- `inverseSquareSingleReverseBefore16Candidate_mem_before16Window`
- `inverseSquareSingleReverseAfter32BandWindowLower`
- `inverseSquareSingleReverseAfter32BandWindowUpper`
- `inverseSquareSingleReverseAfter32BandWindowLower_zero`
- `inverseSquareSingleReverseAfter32BandWindowUpper_zero`
- `inverseSquareSingleReverseAfter32BandWindowLower_final`
- `inverseSquareSingleReverseAfter32BandWindowUpper_final`
- `inverseSquareSingleReverseAfter32Band31To17WindowEndpointCertificateBool`
- `inverseSquareSingleReverseAfter32Band31To17WindowEndpointCertificateBool_eq_true`
- `inverseSquareSingleReverseAfter32Band31To17WindowEndpointCertificate`
- `inverseSquareSingleReverseAfter32BandWindow_round_step_mem`
- `inverseSquareSingleReverseAfter32BandWindow_prefix_mem`
- `inverseSquareSingleReverseAfter32Band31ToBefore16Window`
- `inverseSquareSingleReverseAfter32Band31ToBefore16Window_closed`
- `inverseSquareSingleReverseAfter32Candidate_band31_to_before16_mem_before16Window`
- `inverseSquareSingleReverseBefore16WindowMapsToPrinted`
- `inverseSquareSingleReverseAfter32WindowMapsToPrinted_of_band31_to_before16Window`
- `inverseSquareSingleReverseAfter32WindowMapsToPrinted_of_before16Window`
- `inverseSquareSingleReverseBefore32WindowMapsToPrinted_of_before16Window`
- `inverseSquareSingleReverseBefore64WindowMapsToPrinted_of_before16Window`
- `inverseSquareSingleReverseBefore128WindowMapsToPrinted_of_before16Window`
- `inverseSquareSingleReverseBefore256WindowMapsToPrinted_of_before16Window`
- `inverseSquareSingleReverseBefore512WindowMapsToPrinted_of_before16Window`
- `inverseSquareSingleReverseBefore1024WindowMapsToPrinted_of_before16Window`
- `inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before16Window`
- `inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before16Window`
- `inverseSquareSingleReverseAfter16CandidateWindowLower`
- `inverseSquareSingleReverseAfter16CandidateWindowUpper`
- `inverseSquareSingleReverseAfter16Candidate_mem_after16Window`
- `inverseSquareSingleReverseBefore16Window_add_16_term_mem_after16Window`
- `inverseSquareSingleReverseBefore16Window_round_16_step_mem_after16Window`
- `inverseSquareSingleReverseAfter16WindowMapsToPrinted`
- `inverseSquareSingleReverseBefore16WindowMapsToPrinted_of_after16Window`
- `inverseSquareSingleReverseBefore8CandidateWindowLower`
- `inverseSquareSingleReverseBefore8CandidateWindowUpper`
- `inverseSquareSingleReverseBefore8Candidate_mem_before8Window`
- `inverseSquareSingleReverseAfter16BandWindowLower`
- `inverseSquareSingleReverseAfter16BandWindowUpper`
- `inverseSquareSingleReverseAfter16BandWindowLower_zero`
- `inverseSquareSingleReverseAfter16BandWindowUpper_zero`
- `inverseSquareSingleReverseAfter16BandWindowLower_final`
- `inverseSquareSingleReverseAfter16BandWindowUpper_final`
- `inverseSquareSingleReverseAfter16Band15To9WindowEndpointCertificateBool`
- `inverseSquareSingleReverseAfter16Band15To9WindowEndpointCertificateBool_eq_true`
- `inverseSquareSingleReverseAfter16Band15To9WindowEndpointCertificate`
- `inverseSquareSingleReverseAfter16BandWindow_round_step_mem`
- `inverseSquareSingleReverseAfter16BandWindow_prefix_mem`
- `inverseSquareSingleReverseAfter16Band15ToBefore8Window`
- `inverseSquareSingleReverseAfter16Band15ToBefore8Window_closed`
- `inverseSquareSingleReverseAfter16Candidate_band15_to_before8_mem_before8Window`
- `inverseSquareSingleReverseBefore8WindowMapsToPrinted`
- `inverseSquareSingleReverseAfter16WindowMapsToPrinted_of_band15_to_before8Window`
- `inverseSquareSingleReverseAfter16WindowMapsToPrinted_of_before8Window`
- `inverseSquareSingleReverseBefore16WindowMapsToPrinted_of_before8Window`
- `inverseSquareSingleReverseBefore32WindowMapsToPrinted_of_before8Window`
- `inverseSquareSingleReverseBefore64WindowMapsToPrinted_of_before8Window`
- `inverseSquareSingleReverseBefore128WindowMapsToPrinted_of_before8Window`
- `inverseSquareSingleReverseBefore256WindowMapsToPrinted_of_before8Window`
- `inverseSquareSingleReverseBefore512WindowMapsToPrinted_of_before8Window`
- `inverseSquareSingleReverseBefore1024WindowMapsToPrinted_of_before8Window`
- `inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before8Window`
- `inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before8Window`
- `inverseSquareSingleReverseAfter8CandidateWindowLower`
- `inverseSquareSingleReverseAfter8CandidateWindowUpper`
- `inverseSquareSingleReverseAfter8Candidate_mem_after8Window`
- `inverseSquareSingleReverseBefore8Window_add_8_term_mem_after8Window`
- `inverseSquareSingleReverseBefore8Window_round_8_step_mem_after8Window`
- `inverseSquareSingleReverseAfter8WindowMapsToPrinted`
- `inverseSquareSingleReverseBefore8WindowMapsToPrinted_of_after8Window`
- `inverseSquareSingleReverseBefore4CandidateWindowLower`
- `inverseSquareSingleReverseBefore4CandidateWindowUpper`
- `inverseSquareSingleReverseBefore4Candidate_mem_before4Window`
- `inverseSquareSingleReverseAfter8BandWindowLower`
- `inverseSquareSingleReverseAfter8BandWindowUpper`
- `inverseSquareSingleReverseAfter8BandWindowLower_zero`
- `inverseSquareSingleReverseAfter8BandWindowUpper_zero`
- `inverseSquareSingleReverseAfter8BandWindowLower_final`
- `inverseSquareSingleReverseAfter8BandWindowUpper_final`
- `inverseSquareSingleReverseAfter8Band7To5WindowEndpointCertificateBool`
- `inverseSquareSingleReverseAfter8Band7To5WindowEndpointCertificateBool_eq_true`
- `inverseSquareSingleReverseAfter8Band7To5WindowEndpointCertificate`
- `inverseSquareSingleReverseAfter8BandWindow_round_step_mem`
- `inverseSquareSingleReverseAfter8BandWindow_prefix_mem`
- `inverseSquareSingleReverseAfter8Band7ToBefore4Window`
- `inverseSquareSingleReverseAfter8Band7ToBefore4Window_closed`
- `inverseSquareSingleReverseAfter8Candidate_band7_to_before4_mem_before4Window`
- `inverseSquareSingleReverseBefore4WindowMapsToPrinted`
- `inverseSquareSingleReverseAfter4WindowLower`
- `inverseSquareSingleReverseAfter4WindowUpper`
- `inverseSquareSingleReverseAfter3WindowLower`
- `inverseSquareSingleReverseAfter3WindowUpper`
- `inverseSquareSingleReverseBefore4Window_add_4_term_mem_after4Window`
- `inverseSquareSingleReverseBefore4Window_round_4_step_mem_after4Window`
- `inverseSquareSingleReverseAfter4Window_round_3_step_mem_after3Window`
- `inverseSquareSingleReverseAfter3Window_round_2_step_eq_after2`
- `inverseSquareSingleReverseBefore4WindowMapsToPrinted_closed`
- `inverseSquareSingleReverseAfter8WindowMapsToPrinted_of_band7_to_before4Window`
- `inverseSquareSingleReverseAfter8WindowMapsToPrinted_of_before4Window`
- `inverseSquareSingleReverseAfter8WindowMapsToPrinted_closed`
- `inverseSquareSingleReverseBefore8WindowMapsToPrinted_of_before4Window`
- `inverseSquareSingleReverseBefore8WindowMapsToPrinted_closed`
- `inverseSquareSingleReverseBefore16WindowMapsToPrinted_of_before4Window`
- `inverseSquareSingleReverseBefore32WindowMapsToPrinted_of_before4Window`
- `inverseSquareSingleReverseBefore64WindowMapsToPrinted_of_before4Window`
- `inverseSquareSingleReverseBefore128WindowMapsToPrinted_of_before4Window`
- `inverseSquareSingleReverseBefore256WindowMapsToPrinted_of_before4Window`
- `inverseSquareSingleReverseBefore512WindowMapsToPrinted_of_before4Window`
- `inverseSquareSingleReverseBefore1024WindowMapsToPrinted_of_before4Window`
- `inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before4Window`
- `inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before4Window`
- `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_candidateWindow_certificates`
- `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_eq_exact_candidateWindow`
- `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_eq_candidateWindow`
- `inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before1024Window`
- `inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before512Window`
- `inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before256Window`
- `inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before128Window`
- `inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before64Window`
- `inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before32Window`
- `inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before16Window`
- `inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before8Window`
- `inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before4Window`
- `inverseSquareSingleReverseCandidateWindowMapsToPrinted_closed`
- `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_mem_candidateWindow_closed`
- `inverseSquareSingleReverseHighPrefixCandidateWindowMargin`
- `inverseSquareSingleReverseHighPrefixCandidateWindowMargin_nonneg`
- `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_abs_error_le_candidateWindowMargin`
- `inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound`
- `inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound_nonneg`
- `inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound_le_margin`
- `inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound`
- `inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound_nonneg`
- `inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound_pos`
- `inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound_lt_inv_4096`
- `inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound_le_cellGuardMarginShiftedLowerBound`
- `inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound_lt_cellGuardMarginShiftedLowerBound`
- `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowMarginTarget`
- `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget`
- `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuard_of_abs_error_lt_cellGuardMarginShiftedLowerBound`
- `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuard_of_cellGuardMarginTarget`
- `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget_of_candidateWindowMarginTarget`
- `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget_of_eq_exact`
- `inverseSquareSingleReverseTenPowNineHighPrefix_singleGammaGuard_not_valid`
- `inverseSquareSingleReverseTenPowNineHighPrefix_singleGammaValid_not_valid`
- `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowMarginShiftedLowerBound_lt_coarseAccumulatedStdError`
- `inverseSquareSingleReverseTenPowNineHighPrefix_coarseAccumulatedStdErrorGuard_not_sufficient`
- `inverseSquareSingleReverseTenPowNineHighPrefixCandidate_abs_error_le_candidateWindowMarginShiftedLowerBound`
- `inverseSquareSingleReverseTenPowNineHighPrefixCandidate_abs_error_lt_cellGuardMarginShiftedLowerBound`
- `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowMarginTarget_of_eq_candidate`
- `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget_of_eq_candidate`
- `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_abs_error_le_candidateWindowMarginShiftedLowerBound`
- `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_candidateWindowMarginTarget`
- `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_abs_error_lt_cellGuardMarginShiftedLowerBound`
- `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_cellGuardMarginTarget`
- `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_abs_error_le_candidateWindowMarginShiftedLowerBound_closed`
- `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_candidateWindowMarginTarget_closed`
- `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_candidateWindowCellGuard_closed`
- `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_cellGuardMarginTarget_closed`
- `inverseSquareSingleReverseHighPrefixCandidateWindow_abs_error_le_shiftedMarginLowerBound`
- `inverseSquareSingleReverseTenPowNineHighPrefix_abs_error_le_shiftedMarginLowerBound_of_mem_candidateWindow`
- `inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow_of_abs_error_le_shiftedMarginLowerBound`
- `inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow_of_mem_candidateWindow`
- `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_abs_error_le_shiftedMarginLowerBound`
- `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_mem_candidateWindow`
- `inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow_of_abs_error_le_margin`
- `inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow_of_abs_error_le_marginLowerBound`
- `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_eq_exact`
- `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_eq_exact_tight`
- `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_abs_error_le_margin`
- `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_abs_error_le_marginLowerBound`
- `inverseSquareSingleEarlyMantissaIncrement`
- `inverseSquareSingleEarlyMantissaPrefix`
- `inverseSquareSingleEarlyMantissaPrefix_2895_eq`
- `inverseSquareSingleEarlyMantissaPrefix_2895_add_base_eq_preWindow`
- `inverseSquareSingleEarlyMantissaIncrementNearestCertificateBool`
- `inverseSquareSingleEarlyMantissaIncrementNearestCertificateBool_eq_true`
- `inverseSquareSingleEarlyMantissaIncrementNearestCertificate`
- `inverseSquareSingle_pred_lt_add_of_scaled_left_bound`
- `inverseSquareSingle_add_lt_succ_of_scaled_right_bound`
- `inverseSquareSingle_right_closer_to_target_of_scaled_left_bound`
- `inverseSquareSingle_left_closer_to_target_of_scaled_right_bound`
- `inverseSquareSingle_add_term_rounds_to_nearest_mantissa_of_scaled_bounds`
- `inverseSquareSingleForwardAccumulator_one_eq_one`
- `inverseSquareSingleEarlyMantissaIncrementRule`
- `inverseSquareSingleEarlyMantissaIncrementRule_closed`
- `inverseSquareSingleForwardAccumulator_2896_eq_prePlateauWindowStart_of_early_mantissa_increment_rule`
- `inverseSquareSingleForwardAccumulator_2896_eq_prePlateauWindowStart`
- `inverseSquareSingleForwardStep_normalizedValue_succ_of_index_range`
- `inverseSquareSingleForwardAccumulatorFrom_normalizedValue_of_index_window`
- `inverseSquareSingleForwardAccumulatorFrom_prePlateauWindowStart_2897_of_le_1194`
- `inverseSquareSingleForwardAccumulatorFrom_prePlateauWindowStart_2897_1194_eq_sixBeforePlateau`
- `inverseSquareSingleForwardAccumulatorFrom_sixBeforePlateau_4091_of_le_5`
- `inverseSquareSingleForwardAccumulatorFrom_sixBeforePlateau_4091_five_eq_prePlateau`
- `inverseSquareSingleForwardAccumulatorFrom_sixBeforePlateau_4091_six_eq_plateau`
- `inverseSquareSingleForwardAccumulatorFrom_sixBeforePlateau_4091_six_add_eq_plateau`
- `inverseSquareSingleForwardAccumulatorFrom_prePlateauWindowStart_2897_lt_plateau_of_lt_1200`
- `inverseSquareSingleForwardAccumulatorFrom_prePlateauWindowStart_2897_1200_add_eq_plateau`
- `inverseSquareSingleForwardAccumulator_2896_add_lt_plateau_of_2896_eq_prePlateauWindowStart`
- `inverseSquareSingleForwardAccumulator_4096_add_eq_plateau_of_2896_eq_prePlateauWindowStart`
- `inverseSquareSingleForwardAccumulator_2896_add_lt_plateau_of_early_mantissa_increment_rule`
- `inverseSquareSingleForwardAccumulator_2896_add_lt_plateau`
- `inverseSquareSingleForwardAccumulator_4096_add_eq_plateau_of_early_mantissa_increment_rule`
- `inverseSquareSingleForwardAccumulator_4096_add_eq_plateau`
- `inverseSquareSingleSixBeforePlateau_add_4091_term_rounds_to_fiveBeforePlateau`
- `inverseSquareSingleFiveBeforePlateau_add_4092_term_rounds_to_fourBeforePlateau`
- `inverseSquareSingleFourBeforePlateau_add_4093_term_rounds_to_threeBeforePlateau`
- `inverseSquareSingleThreeBeforePlateau_add_4094_term_rounds_to_twoBeforePlateau`
- `inverseSquareSingleTwoBeforePlateau_add_4095_term_rounds_to_prePlateau`
- `inverseSquareSinglePrePlateau_add_4096_term_rounds_to_plateau`
- `inverseSquareSinglePlateau_add_4096_term_rounds_to_self`
- `inverseSquareSinglePlateau_add_positive_term_le_two_pow_neg_24_rounds_to_self`
- `inverseSquareSinglePlateau_add_term_rounds_to_self_of_ge_4096`
- `increasingPrecisionSinExample`
- `increasingPrecisionSinExampleScale`
- `increasingPrecisionSinExampleFrequency`
- `increasingPrecisionSinExampleSource`
- `increasingPrecisionSinExample_perturbation_abs_le`
- `increasingPrecisionSinExampleSource_perturbation_abs_le`
- `finiteRoundToEven_eq_of_strict_closest`
- `increasingPrecisionSinExample_finiteRoundToEven_eq_base_of_two_abs_scale_lt_spacing`
- `increasingPrecisionSinExampleSource_finiteRoundToEven_eq_base_of_spacing`
- `increasingPrecisionSinExampleSource_ieeeSingle_roundToEven_one`
- `increasingPrecision_ieeeSingle_roundToEven_one_seventh`
- `increasingPrecision_ieeeDouble_roundToEven_one_seventh`
- `increasingPrecision_ieeeSingle_roundToEven_one_seventh_error`
- `increasingPrecision_ieeeDouble_roundToEven_one_seventh_error`
- `increasingPrecision_one_seventh_binary_grid_abs_error_ge`
- `increasingPrecision_one_seventh_binary_grid_abs_error_gt_scale_of_t_le_twenty`
- `increasingPrecision_one_seventh_binary_grid_abs_error_gt_scale_of_t_le_twenty_three`
- `increasingPrecision_one_seventh_binary_grid_lower_bound_lt_scale_at_twenty_four`
- `increasingPrecisionSinExampleSource_perturbation_lt_one_seventh_binary_grid_error_of_t_le_twenty`
- `increasingPrecisionSinExampleSource_perturbation_lt_one_seventh_binary_grid_error_of_t_le_twenty_three`
- `increasingPrecisionExampleY`
- `increasingPrecisionExampleExactZ`
- `increasingPrecisionExampleElseWithExpHat`
- `increasingPrecisionExampleY_two_thirds_eq_zero`
- `increasingPrecisionExampleY_ne_zero_of_ne_two_thirds`
- `increasingPrecisionExampleY_pos_of_ne_two_thirds`
- `increasingPrecisionExampleExactZ_two_thirds_eq_one`
- `increasingPrecisionExampleElseWithExpHat_one_eq_zero`
- `increasingPrecisionExampleElse_relError_one_of_expHat_one`
- `increasingPrecisionExampleElse_two_precision_failure_of_expHat_one`
- `increasingPrecisionExampleElse_two_precision_failure_of_stored_inputs_expHat_one`
- `increasingPrecision_ieeeSingle_roundToEven_two_thirds`
- `increasingPrecision_ieeeDouble_roundToEven_two_thirds`
- `increasingPrecisionExampleY_ieeeSingle_roundToEven_two_thirds`
- `increasingPrecisionExampleY_ieeeDouble_roundToEven_two_thirds`
- `increasingPrecision_ieeeSingle_roundToEven_exp_branch_y_eq_one`
- `increasingPrecision_ieeeDouble_roundToEven_exp_branch_y_eq_one`
- `increasingPrecisionExampleElse_two_precision_failure_of_ieee_roundToEven_stored_exp_source`
- `increasingPrecisionExampleElse_two_precision_failure_of_ieee_finite_stored_inputs_expHat_one`
- `increasingPrecisionExampleElse_two_precision_failure_of_ieee_roundToEven_stored_source_expHat_one`
- `expm1Algorithm1Exact`, `expm1Algorithm2Exact`
- `expm1Algorithm1Exact_zero`, `expm1Algorithm2Exact_zero`
- `expm1Algorithm2Exact_eq_algorithm1Exact`
- `expm1Table12X`, `expm1Table12Algorithm1`, `expm1Table12Algorithm2`
- `expm1Table12Algorithm2TenPowNeg15Corrected`
- `expm1Table12_x_rows`
- `expm1Table12_algorithm1_rows`
- `expm1Table12_algorithm2_rows`
- `expm1Table12_algorithm2_ten_pow_neg15_last_digit_correction`
- `expm1Page23_displayed_single_precision_ratio`
- `expm1Page23_displayed_exact_arithmetic_ratio`
- `expm1Algorithm2RoundedCore`
- `expm1LogRatio`
- `expm1LogRatio_tendsto_one`
- `expm1LogRatioDenRemainder`
- `expm1Log_one_add_sub_linear_quadratic_abs_le`
- `expm1LogRatioDenRemainder_abs_le`
- `expm1LogRatio_one_add_eq_inv_one_sub_half_add_remainder`
- `expm1LogRatio_one_add_sub_one_add_half_abs_le`
- `expm1LogRatio_one_add_sub_one_abs_le`
- `expm1LogRatio_sub_one_abs_le`
- `expm1LogRatio_abs_ge_one_sub_radius_bound`
- `expm1LogRatio_abs_ge_half_of_radius`
- `expm1LogRatio_one_add_self_sub_abs_le`
- `expm1LogRatio_self_sub_abs_le`
- `expm1LogRatio_one_add_diff_sub_half_abs_le`
- `expm1LogRatio_mul_one_add_delta_diff_sub_y_delta_half_abs_le`
- `expm1LogRatio_mul_one_add_delta_diff_sub_delta_half_abs_le`
- `expm1LogRatio_mul_one_add_delta_diff_sub_logRatio_delta_half_abs_le`
- `expm1Algorithm2_yhat_eq_one_implies_x_eq_neg_log_one_add_delta`
- `expm1Algorithm2RoundedCore_eq_source_1_9`
- `expm1Algorithm2RoundedCore_eq_source_1_9_of_exact_sub`
- `expm1Algorithm2RoundedCore_eq_source_1_9_of_guardDigitSubtractionModel`
- `expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_ferguson`
- `expm1Algorithm2_yhat_one_sterbenzRatioCondition_of_abs_sub_one_le_third`
- `expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_sterbenz_radius`
- `expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_exp_perturb_sterbenz_radius`
- `expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_exp_x_sterbenz_radius`
- `expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_exp_x_mul_one_add_u_sterbenz`
- `expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_exact_sub`
- `expm1Algorithm2RoundedCore_relError_le_gamma2_of_exact_sub`
- `expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_sterbenz_radius`
- `expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_perturb_sterbenz_radius`
- `expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_x_sterbenz_radius`
- `expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_x_mul_one_add_u_sterbenz`
- `expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_finiteRoundToEven_exp_x_mul_one_add_u_sterbenz`
- `expm1Algorithm2RoundedCore_relError_le_gamma2_of_finiteRoundToEven_exp_x_mul_one_add_u_sterbenz`
- `FloatingPointFormat.finiteRoundToEven_finiteSystem`
- `FloatingPointFormat.finiteRoundToEvenOp_finiteSystem`
- `FloatingPointFormat.finiteRoundToEvenSqrt_finiteSystem`
- `expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_rounded_exp_x_mul_one_add_u_sterbenz`
- `expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_finiteRoundToEven_rounded_exp_x_mul_one_add_u_sterbenz`
- `expm1Algorithm2RoundedCore_relError_le_gamma2_of_finiteRoundToEven_rounded_exp_x_mul_one_add_u_sterbenz`
- `expm1Algorithm2RoundedExp_delta_abs_le_of_finiteNormalRange`
- `expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_finiteNormal_sterbenz`
- `expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_finiteRoundToEven_exp_finiteNormal_sterbenz`
- `expm1Algorithm2RoundedCore_relError_le_gamma2_of_finiteRoundToEven_exp_finiteNormal_sterbenz`
- `expm1Algorithm2RoundedLog_exists_contract_of_finiteNormalRange`
- `expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_finiteRoundToEven_exp_log_finiteNormal_sterbenz`
- `expm1Algorithm2RoundedCore_relError_le_gamma2_of_finiteRoundToEven_exp_log_finiteNormal_sterbenz`
- `finiteRoundToEvenSubtractionLink`
- `finiteRoundToEvenSubtractionLink.sub_one`
- `expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_finiteNormal_sterbenz_of_subtractionLink`
- `expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_finiteRoundToEven_exp_log_finiteNormal_sterbenz_of_subtractionLink`
- `expm1Algorithm2RoundedCore_relError_le_gamma2_of_finiteRoundToEven_exp_log_finiteNormal_sterbenz_of_subtractionLink`
- `expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma4`
- `expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma3`
- `expm1Algorithm2RoundedCore_relError_le_gamma4`
- `expm1Algorithm2RoundedCore_relError_le_gamma3`
- `expm1Algorithm2SlowRatioPerturbationBound`
- `expm1Algorithm2LocalRelErrorBound`
- `expm1Algorithm2RoundedCore_relError_le_local_bound`
- `expm1Algorithm2RoundedCore_relError_le_local_bound_gamma3`
- `expm1Algorithm2LocalRelErrorBound_eq_drift_div_add_gamma4`
- `expm1Algorithm2LocalRelErrorBound_le_eta_add_gamma4`
- `expm1Algorithm2RoundedCore_relError_le_eta_add_gamma4`
- `expm1Algorithm2RoundedCore_relError_le_eta_add_gamma3`
- `expm1Algorithm2PrimitiveDriftBound`
- `expm1Algorithm2PrimitiveSlowRemainderBound`
- `expm1Algorithm2SlowRatioPerturbationBound_le_of_abs_bounds`
- `expm1Algorithm2LocalDrift_le_primitive_bound`
- `expm1Algorithm2PrimitiveDriftBound_le_half_u_mul_abs_logRatio_add_slow_remainder`
- `expm1Algorithm2RoundedCore_relError_le_eta_add_gamma4_of_primitive_bounds`
- `expm1Algorithm2RoundedCore_relError_le_eta_add_gamma3_of_primitive_bounds`
- `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_remainder`
- `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_remainder_of_primitive_bounds`
- `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_local_remainder_of_abs_bounds`
- `expm1Algorithm2PrimitiveSlowRemainderBound_le_of_radius`
- `expm1Algorithm2_yhat_sub_one_abs_le_of_y_radius`
- `expm1Algorithm2_exp_sub_one_abs_le_of_abs_x_le`
- `expm1LogRatio_exp_eq_algorithm1Exact_of_ne_zero`
- `expm1LogRatio_exp_ne_zero_of_ne_zero`
- `expm1Algorithm2_exp_x_combined_radius_le_third_of_exp_mul_one_add_u_le`
- `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_radius_remainder_of_abs_bounds`
- `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_radius_bound_of_abs_bounds`
- `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_perturb_radius_bound`
- `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_x_radius_bound`
- `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_x_mul_one_add_u_bound`
- `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_log_finiteNormal`
- `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_log_finiteNormal_algorithm1Exact`
- `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_u_radius_bound_of_abs_bounds`
- `expm1Algorithm2ThreePointFiveUnitBound`
- `expm1Algorithm2Gamma3Scalar`
- `expm1Algorithm2ThreePointFiveUnitBoundScalar`
- `expm1Algorithm2ThreePointFiveUnitBound_eq_scalar`
- `expm1Algorithm2ThreePointFiveUnitBoundScalar_isBigO`
- `expm1Algorithm2ThreePointFiveUnitBound_eq_zero_of_u_eq_zero`
- `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_u_radius_bound_of_unit_bounds`
- `expm1Algorithm2RoundedCore_relError_le_three_point_five_unit_bound_of_unit_bounds`
- `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_normalized_remainder_of_abs_bounds`
- `givensRotation_mulVec_p`
- `givensRotation_mulVec_q`
- `givensRotation_ratio_zeroes_q`
- `givensRotation_ratio_mulVec_p`
- `givensRotation_trig_orthogonal`
- `givensQRRectangularRotationCount`
- `givensQRRectangularRotationCount_twice_int`
- `givensQRRectangularRotationCount_ten_by_six`
- `powerMethodStep`, `IsRightEigenpair`
- `inverseIterationShiftedMatrix`, `SolvesInverseIterationShiftedSystem`
- `inverseIterationShiftedMatrix_mulVec`
- `inverseIteration_shiftedMatrix_mul_eigenvector`
- `inverseIteration_shiftedSystem_solution_on_eigenvector`
- `inverseIteration_shiftedInverse_mul_eigenvector_of_leftInverse`
- `inverseIteration_shiftedInverse_amplification_abs_eq`
- `inverseIteration_shiftedInverse_amplification_strict_of_abs_shift_lt`
- `matMulVec_smul_right`, `isRightEigenpair_smul`
- `inverseIteration_parallel_error_output_isRightEigenpair`
- `eigenResidualVec`
- `eigenResidualVec_add_parallel_eq`
- `eigenResidualVec_norm_le_opNorm_add_abs`
- `inverseIteration_near_parallel_error_eigenResidual_eq`
- `inverseIteration_near_parallel_error_eigenResidual_norm_le`
- `BinaryTerminating`, `MatrixEntriesBinaryTerminating`, `MatrixEntriesFiniteSystem`
- `five_not_dvd_two_pow_nat`
- `three_not_dvd_two_pow_nat`
- `seven_not_dvd_two_pow_nat`
- `one_fifth_not_binaryTerminating`
- `one_div_ten_pow_succ_not_binaryTerminating`
- `two_thirds_not_binaryTerminating`
- `one_seventh_not_binaryTerminating`
- `ieeeSingleFormat_normalizedSystem_binaryTerminating`
- `ieeeSingleFormat_subnormalSystem_binaryTerminating`
- `ieeeSingleFormat_finiteSystem_binaryTerminating`
- `ieeeDoubleFormat_normalizedSystem_binaryTerminating`
- `ieeeDoubleFormat_subnormalSystem_binaryTerminating`
- `ieeeDoubleFormat_finiteSystem_binaryTerminating`
- `one_fifth_not_ieeeDoubleFiniteSystem`
- `two_thirds_not_ieeeSingleFiniteSystem`
- `two_thirds_not_ieeeDoubleFiniteSystem`
- `one_seventh_not_ieeeSingleFiniteSystem`
- `one_seventh_not_ieeeDoubleFiniteSystem`
- `beneficialPowerMatrix`, `beneficialPowerStart`
- `beneficialPowerCharMatrix`
- `beneficialPowerMatrix_entry_zero_two_eq_one_fifth`
- `beneficialPowerMatrix_entry_zero_two_not_binaryTerminating`
- `beneficialPowerMatrix_entry_zero_two_not_ieeeDoubleFiniteSystem`
- `beneficialPowerMatrix_not_matrixEntriesBinaryTerminating`
- `beneficialPowerMatrix_not_matrixEntriesIeeeDoubleFiniteSystem`
- `ieeeDoubleFormat_one_fifth_finiteNormalRange`
- `ieeeDoubleFormat_one_tenth_finiteNormalRange`
- `ieeeDoubleFormat_two_fifths_finiteNormalRange`
- `ieeeDoubleFormat_three_tenths_finiteNormalRange`
- `ieeeDoubleFormat_three_fifths_finiteNormalRange`
- `ieeeDoubleFormat_seven_tenths_finiteNormalRange`
- `ieeeDoubleFormat_one_fifth_rounds_to`
- `ieeeDoubleFormat_one_tenth_rounds_to`
- `ieeeDoubleFormat_two_fifths_rounds_to`
- `ieeeDoubleFormat_three_tenths_rounds_to`
- `ieeeDoubleFormat_three_fifths_rounds_to`
- `ieeeDoubleFormat_seven_tenths_rounds_to`
- `ieeeDoubleFormat_neg_one_tenth_rounds_to`
- `ieeeDoubleFormat_neg_two_fifths_rounds_to`
- `ieeeDoubleFormat_neg_three_tenths_rounds_to`
- `ieeeDoubleFormat_one_half_finiteSystem`
- `ieeeDoubleFormat_one_half_rounds_to`
- `ieeeDoubleFormat_neg_three_fifths_rounds_to`
- `beneficialPowerMatrixIeeeDoubleRounded`
- `beneficialPowerMatrixIeeeDoubleRoundedFirstStep`
- `beneficialPowerMatrixIeeeDoubleRounded_row_zero_sum_eq`
- `beneficialPowerMatrixIeeeDoubleRounded_row_one_sum_eq`
- `beneficialPowerMatrixIeeeDoubleRounded_row_two_sum_eq`
- `beneficialPowerMatrix_row_sum_zero`
- `beneficialPowerCharDet_eq`
- `beneficialPowerCharDet_root_zero`
- `beneficialPowerCharDet_root_small`
- `beneficialPowerCharDet_root_dominant`
- `beneficialPowerEigenvalueSmall_display_accuracy`
- `beneficialPowerEigenvalueDominant_display_accuracy`
- `beneficialPowerStart_isRightEigenpair_zero`
- `beneficialPowerFirstStep_zero`
- `beneficialPowerMatrixIeeeDoubleRounded_firstStep_zero_component_eq`
- `beneficialPowerMatrixIeeeDoubleRounded_firstStep_one_component_eq`
- `beneficialPowerMatrixIeeeDoubleRounded_firstStep_two_component_eq`
- `beneficialPowerMatrixIeeeDoubleRounded_firstStep_eq`
- `beneficialPowerMatrixIeeeDoubleRounded_firstStep_vecNorm2_pos`
- `beneficialPowerMatrixIeeeDoubleRounded_firstStep_vecNorm2_ge_two_pow_neg54`
- `beneficialPowerShiftedMatrix_mul_start`
- `beneficialPower_inverseIteration_shiftedSystem_solution_start`
- `beneficialPower_shiftedInverse_mul_start_of_leftInverse`
- `beneficialPower_inverseIteration_near_parallel_error_eigenResidual_eq`
- `beneficialPower_inverseIteration_near_parallel_error_eigenResidual_norm_le`
- `beneficialPower_inverseIteration_near_parallel_error_eigenResidual_norm_le_of_residual_norm_le`
- `beneficialPower_inverseIteration_near_parallel_error_eigenResidual_norm_le_of_componentwise_common_scalar`
- `powerMethodStep_add_matrix`
- `beneficialPowerFirstStep_perturbed_eq_delta`
- `beneficialPowerFirstStep_perturbed_eq_zero_iff_row_sums_zero`
- `beneficialPowerFirstStep_perturbed_nonzero_of_delta_row_sum_ne_zero`
- `vecNorm2_pos_of_exists_ne`
- `beneficialPowerFirstStep_perturbed_vecNorm2_pos_of_delta_row_sum_ne_zero`
- `beneficialPowerFirstStep_perturbed_vecNorm2_eq_zero_iff_row_sums_zero`
- `beneficialPowerFirstStep_perturbed_vecNorm2_ge_of_row_sum_abs_ge`
- `beneficialPowerFirstStep_perturbed_vecNorm2_le_of_row_sum_abs_le`
- `beneficialPowerFirstStep_perturbed_vecNorm2_le_of_entry_abs_le`
- `IsUpperHessenbergMatrix`
- `hessenbergDiagExactStep`, `hessenbergDiagRoundedStep`
- `HessenbergRoundedDiagTraceOnOriginal`
- `HessenbergExactDiagTraceOnEntrywisePerturbation`
- `hessenbergDiagRoundedStep_eq_perturbed_exactStep`
- `hessenbergEntrywisePerturbation`
- `hessenbergEntrywisePerturbation_diag`
- `hessenbergEntrywisePerturbation_subdiag`
- `hessenbergSubdiagPerturbationFactors`
- `hessenbergSubdiagPerturbationFactors_prod`
- `hessenbergEntrywisePerturbation_isUpperHessenberg`
- `hessenbergEntrywisePerturbation_diag_signedRelErrorWitness`
- `hessenbergEntrywisePerturbation_diag_abs_error_le`
- `hessenbergEntrywisePerturbation_subdiag_signedRelErrorWitness_exists`
- `hessenbergEntrywisePerturbation_subdiag_abs_error_le_gamma`
- `hessenbergEntrywisePerturbation_abs_error_le_gamma_three`
- `hessenbergDiagRoundedStep_eq_entrywisePerturbedExactStep`
- `hessenbergRoundedDiagTraceOnOriginal_exactTraceOnEntrywisePerturbation`
- `hessenbergDetRoundedProduct`
- `hessenbergDetRoundedProduct_signedRelError`
- `hessenbergDetRoundedProduct_relError_eq`
- `hessenbergDetRoundedProduct_relError_le_gamma`
- `hessenbergDetRoundedProduct_relError_le_gamma_of_det_eq_diag_prod`
- `hessenbergRoundedDiagTraceOnOriginal_nearbyDet_relError_le_gamma`
- `hessenberg4NoPivotPivot0`
- `hessenberg4NoPivotMultiplier10`
- `hessenberg4NoPivotDiag1`
- `hessenberg4NoPivotSuper12`
- `hessenberg4NoPivotSuper13`
- `hessenberg4NoPivotMultiplier21`
- `hessenberg4NoPivotDiag2`
- `hessenberg4NoPivotSuper23`
- `hessenberg4NoPivotMultiplier32`
- `hessenberg4NoPivotDiag3`
- `hessenberg4NoPivotDiag`
- `hessenberg4NoPivotEndpoint`
- `hessenberg4NoPivotEndpoint_blockTriangular`
- `hessenberg4NoPivotEndpoint_det_eq_diag_prod`
- `hessenberg4NoPivotPrevSuper`
- `hessenberg4NoPivotPrevPivot`
- `hessenberg4NoPivotDiag_exactTraceOnMatrix`
- `hessenberg4NoPivotDiag_exactTraceOnEntrywisePerturbation`
- `hessenberg4NoPivotStage1`
- `hessenberg4NoPivotStage2`
- `hessenberg4NoPivotStage3`
- `hessenberg4NoPivotStage1_det_eq`
- `hessenberg4NoPivotStage2_det_eq`
- `hessenberg4NoPivotStage3_det_eq`
- `hessenberg4NoPivotStage3_eq_endpoint`
- `hessenberg4NoPivotEndpoint_det_eq_of_upperHessenberg`
- `hessenberg4NoPivot_det_eq_diag_prod_of_upperHessenberg`
- `hessenberg4NoPivotEntrywisePerturbation_det_eq_diag_prod_of_upperHessenberg`
- `hessenberg4NoPivotRoundedTrace_nearbyDet_relError_le_gamma`
- `hessenbergDetExampleMatrix`, `hessenbergDetExampleOnes`
- `hessenbergDetExampleRhs`, `hessenbergDetExampleMatrixInv`
- `hessenbergDetExample_isUpperHessenberg`
- `hessenbergDetExample_mul_ones`
- `hessenbergDetExample_ones_solves_rhs`
- `hessenbergDetExampleMatrixInv_alpha_ten_pow_isInverse`
- `hessenbergDetExampleMatrix_alpha_ten_pow_infNorm_eq`
- `hessenbergDetExampleMatrixInv_alpha_ten_pow_infNorm_eq`
- `hessenbergDetExample_kappaInfProduct_alpha_ten_pow_eq`
- `hessenbergDetExample_kappaInfProduct_alpha_ten_pow_near_sixteen`
- `hessenbergDetExampleNoPivotUDiag`
- `hessenbergDetExampleNoPivotU`
- `hessenbergDetExampleNoPivotU_blockTriangular`
- `hessenbergDetExampleNoPivotU_det_eq_diag_prod`
- `hessenbergDetExampleNoPivotUDiag_prod_eq`
- `hessenbergDetExampleMatrix_det_eq_noPivotUDiag_prod`
- `hessenbergDetExampleMatrix_det_eq`
- `hessenbergDetExampleRoundedProduct_relError_le_gamma`
- `hessenbergDetExampleMatrix_alpha_ten_pow_det_eq`
- `hessenbergDetExampleMatrix_alpha_ten_pow_det_near_two`
- `hessenbergDetExample_alpha_ten_pow_exact_table_baseline`
- `hessenbergDetExampleTable13IeeeSingleFormat`
- `hessenbergDetExampleTable13SourceAlpha`
- `hessenbergDetExampleTable13StoredAlpha`
- `hessenbergDetExampleTable13StoredMatrix`
- `hessenbergDetExampleTable13StoredRhs`
- `hessenbergDetExampleTable13IeeeSingle_one_finiteSystem`
- `hessenbergDetExampleTable13IeeeSingle_two_finiteSystem`
- `hessenbergDetExampleTable13IeeeSingle_round_zero`
- `hessenbergDetExampleTable13IeeeSingle_round_one`
- `hessenbergDetExampleTable13IeeeSingle_round_neg_one`
- `hessenbergDetExampleTable13IeeeSingle_round_two`
- `hessenbergDetExampleTable13StoredAlpha_finiteSystem`
- `hessenbergDetExampleTable13StoredAlpha_eq_normalizedValue`
- `hessenbergDetExampleTable13StoredAlpha_eq`
- `hessenbergDetExampleTable13StoredAlpha_pos`
- `hessenbergDetExampleTable13StoredAlpha_ne_zero`
- `hessenbergDetExampleTable13StoredMatrix_finiteSystem`
- `hessenbergDetExampleTable13StoredRhs_finiteSystem`
- `hessenbergDetExampleTable13_storedMatrix_eq_storedAlpha_matrix`
- `hessenbergDetExampleTable13StoredMatrix_isUpperHessenberg`
- `hessenbergDetExampleTable13StoredMatrix_pivot0_ne_zero`
- `hessenbergDetExampleTable13StoredMatrix_det_eq`
- `hessenbergDetExampleTable13StoredMatrix_det_eq_noPivotUDiag_prod`
- `hessenbergDetExampleTable13_round_one_div_storedAlpha`
- `hessenbergDetExampleTable13StoredMatrix_firstMultiplier_rounds_to_ten_pow_seven`
- `hessenbergDetExampleTable13IeeeSingle_ten_pow_seven_finiteSystem`
- `hessenbergDetExampleTable13IeeeSingle_neg_ten_pow_seven_finiteSystem`
- `hessenbergDetExampleTable13IeeeSingle_firstStageDiag_finiteSystem`
- `hessenbergDetExampleTable13IeeeSingle_firstStageSuper_finiteSystem`
- `hessenbergDetExampleTable13_round_ten_pow_seven_mul_neg_one`
- `hessenbergDetExampleTable13_round_one_sub_neg_ten_pow_seven`
- `hessenbergDetExampleTable13_round_neg_one_sub_neg_ten_pow_seven`
- `hessenbergDetExampleTable13StoredMatrix_firstStage_diag11_rounds_to`
- `hessenbergDetExampleTable13StoredMatrix_firstStage_super12_rounds_to`
- `hessenbergDetExampleTable13StoredMatrix_firstStage_super13_rounds_to`
- `hessenbergDetExampleTable13_round_one_div_firstStageDiag_eq_normalizedValue`
- `hessenbergDetExampleTable13_round_one_div_firstStageDiag`
- `hessenbergDetExampleTable13StoredMatrix_secondMultiplier_rounds_to`
- `hessenbergDetExampleTable13IeeeSingle_secondStageProduct_finiteSystem`
- `hessenbergDetExampleTable13IeeeSingle_secondStageDiag_finiteSystem`
- `hessenbergDetExampleTable13IeeeSingle_secondStageSuper_finiteSystem`
- `hessenbergDetExampleTable13_round_secondMultiplier_mul_firstStageSuper`
- `hessenbergDetExampleTable13_round_one_sub_secondStageProduct`
- `hessenbergDetExampleTable13_round_neg_one_sub_secondStageProduct`
- `hessenbergDetExampleTable13StoredMatrix_secondStage_diag22_rounds_to`
- `hessenbergDetExampleTable13StoredMatrix_secondStage_super23_rounds_to`
- `hessenbergDetExampleTable13IeeeSingle_thirdMultiplier_finiteSystem`
- `hessenbergDetExampleTable13IeeeSingle_thirdStageProduct_finiteSystem`
- `hessenbergDetExampleTable13IeeeSingle_finalDiag_finiteSystem`
- `hessenbergDetExampleTable13_round_one_div_secondStageDiag`
- `hessenbergDetExampleTable13_round_thirdMultiplier_mul_secondStageSuper`
- `hessenbergDetExampleTable13_round_one_sub_thirdStageProduct`
- `hessenbergDetExampleTable13StoredMatrix_thirdMultiplier_rounds_to`
- `hessenbergDetExampleTable13StoredMatrix_finalDiag_rounds_to`
- `hessenbergDetExampleTable13IeeeSingle_detProduct01_finiteSystem`
- `hessenbergDetExampleTable13IeeeSingle_detProduct012_finiteSystem`
- `hessenbergDetExampleTable13IeeeSingle_detProduct_finiteSystem`
- `hessenbergDetExampleTable13_round_storedAlpha_mul_firstStageDiag`
- `hessenbergDetExampleTable13_round_detProduct01_mul_secondStageDiag`
- `hessenbergDetExampleTable13_round_detProduct012_mul_finalDiag`
- `hessenbergDetExampleTable13_detProduct_leftToRight_rounds_to`
- `hessenbergDetExampleTable13_detProduct_relError_eq`
- `hessenbergDetExampleTable13_storedRhs_rows`
- `hessenbergDetExampleTable13_round_sourceAlpha_sub_three`
- `hessenbergDetExampleTable13StoredRhs0_eq_neg_three`
- `hessenbergDetExampleTable13_round_ten_pow_seven_mul_neg_three`
- `hessenbergDetExampleTable13_round_zero_sub_neg_thirty_million`
- `hessenbergDetExampleTable13StoredRhs_firstStage_rhs1_rounds_to`
- `hessenbergDetExampleTable13_round_secondMultiplier_mul_firstStageRhs`
- `hessenbergDetExampleTable13_round_one_sub_secondRhsProduct`
- `hessenbergDetExampleTable13StoredRhs_secondStage_rhs2_rounds_to`
- `hessenbergDetExampleTable13_round_thirdMultiplier_mul_secondStageRhs`
- `hessenbergDetExampleTable13_round_two_sub_thirdRhsProduct`
- `hessenbergDetExampleTable13StoredRhs_finalStage_rhs3_rounds_to`
- `hessenbergDetExampleTable13_backSub_x3_rounds_to_one`
- `hessenbergDetExampleTable13_backSub_x2_rounds_to_one`
- `hessenbergDetExampleTable13_backSub_row1_firstSub_rounds_to`
- `hessenbergDetExampleTable13_backSub_x1_rounds_to_one`
- `hessenbergDetExampleTable13_backSub_x0_rounds_to_zero`
- `hessenbergDetExampleTable13_standardBackSubSolution_rows`
- `hessenbergDetExampleTable13ComputedSolution`
- `hessenbergDetExampleTable13SolutionRelativeError`
- `hessenbergDetExampleTable13ExactDetDisplay`
- `hessenbergDetExampleTable13ComputedDetDisplay`
- `hessenbergDetExampleTable13DetRelativeError`
- `hessenbergDetExampleTable13_standardBackSub_first_component_ne_printed`
- `hessenbergDetExampleTable13AltStoredRhs0`
- `hessenbergDetExampleTable13AltStoredRhs0_finiteSystem`
- `hessenbergDetExampleTable13AltStoredRhs0_gt_neg_three`
- `hessenbergDetExampleTable13AltStoredRhs0_eq_normalizedValue`
- `hessenbergDetExampleTable13_neg_three_altStoredRhs0_adjacent`
- `hessenbergDetExampleTable13StoredRhs0_lt_altStoredRhs0`
- `hessenbergDetExampleTable13StoredRhs0_ne_altStoredRhs0`
- `hessenbergDetExampleTable13IeeeSingle_altRow0SecondSub_finiteSystem`
- `hessenbergDetExampleTable13_altRhsBackSub_row0_firstSub_rounds_to`
- `hessenbergDetExampleTable13_altRhsBackSub_row0_secondSub_rounds_to`
- `hessenbergDetExampleTable13_altRhsBackSub_row0_thirdSub_rounds_to`
- `hessenbergDetExampleTable13_altRhsBackSub_row0_div_rounds_to`
- `hessenbergDetExampleTable13_altRhsBackSub_x0_rounds_to_printed_float`
- `hessenbergDetExampleTable13_altRhsBackSub_first_component_matches_printed`
- `hessenbergDetExampleTable13_computedSolution_rows`
- `hessenbergDetExampleTable13_exactSolution_rows`
- `hessenbergDetExampleTable13_det_rows`
- `hessenbergDetExampleTable13_detProduct_computedDisplay_near`
- `hessenbergDetExampleTable13_detProduct_relError_matches_display`
- `hessenbergDetExampleTable13_exactSolution_infNorm_eq`
- `hessenbergDetExampleTable13_solutionError_infNorm_eq`
- `hessenbergDetExampleTable13_solution_relative_error_eq`
- `hessenbergDetExampleTable13_first_component_abs_error_gt_one`
- `hessenbergDetExampleTable13_solution_relative_error_gt_one`
- `hessenbergDetExampleTable13_det_relative_error_lt_two_eight`
- `hessenbergDetExampleTable13Residual`
- `hessenbergDetExampleTable13_residual_rows`
- `hessenbergDetExampleTable13_computedSolution_infNorm_eq`
- `hessenbergDetExampleTable13_residual_infNorm_eq`
- `hessenbergDetExampleTable13_scaled_residual_eq`
- `hessenbergDetExampleTable13_scaled_residual_gt_one_tenth`
- `hessenbergDetExample_alpha_ten_pow_roundedProduct_relError_le_gamma`
- `hessenbergDetExampleFirstMultiplier`
- `hessenbergDetExampleFirstMultiplier_eq`
- `hessenbergDetExampleFirstMultiplier_alpha_ten_pow`
- `kahanHornerNumerator`, `kahanHornerDenominator`
- `kahanRationalFunction`, `kahanHornerGridPoint`
- `flKahanHornerNumerator`, `flKahanHornerDenominator`
- `flKahanRationalFunction`
- `kahanIeeeDoubleUnitRoundoff`
- `ieeeDoubleKahanNumerator_m0`, `ieeeDoubleKahanNumerator_s0`
- `ieeeDoubleKahanNumerator_m1`, `ieeeDoubleKahanNumerator_s1`
- `ieeeDoubleKahanNumerator_m2`, `ieeeDoubleKahanNumerator_s2`
- `ieeeDoubleKahanNumerator_m3`
- `ieeeDoubleKahanHornerNumerator`
- `ieeeDoubleKahanDenominator_s0`, `ieeeDoubleKahanDenominator_m1`
- `ieeeDoubleKahanDenominator_s1`, `ieeeDoubleKahanDenominator_m2`
- `ieeeDoubleKahanDenominator_s2`, `ieeeDoubleKahanDenominator_m3`
- `ieeeDoubleKahanHornerDenominator`
- `ieeeDoubleKahanRationalFunction`
- `IeeeDoubleKahanNumeratorNormalTrace`
- `IeeeDoubleKahanDenominatorNormalTrace`
- `IeeeDoubleKahanQuotientNormalTrace`
- `kahanHornerNumeratorErrorEval`, `kahanHornerDenominatorErrorEval`
- `kahanHornerNumerator_eq_poly`
- `kahanHornerDenominator_eq_poly`
- `kahanHornerNumerator_shifted_eq`
- `kahanHornerDenominator_shifted_eq`
- `kahanHornerGridPoint_one`
- `kahanHornerGridPoint_succ_sub`
- `kahanHornerGridPoint_three_sixty_one`
- `kahanHornerGridPoint_mem_source_interval`
- `kahanHornerGridPoint_pairwise_distance_le_source_width`
- `kahanHornerDenominator_grid_one_pos`
- `kahanHornerDenominator_gt_three_on_source_grid_interval`
- `kahanHornerDenominator_pos_on_source_grid_interval`
- `kahanHornerDenominator_grid_pos_of_one_le_of_le_three_sixty_one`
- `kahanRationalFunctionFirstDiffKernel`
- `kahanRationalFunctionFirstDiffKernel_abs_lt_one`
- `kahanRationalFunction_first_diff_num_factor`
- `kahanRationalFunction_source_interval_variation_from_first_lt`
- `kahanRationalFunction_grid_variation_from_first_lt`
- `kahanRationalFunction_grid_pair_variation_lt_two`
- `kahanRoundedGrid_error_spread_gt_of_output_spread`
- `ieeeDoubleKahanRationalFunction_grid_error_spread_gt_of_output_spread`
- `kahanRationalFunction_first_to_last_variation_lt`
- `kahanRoundedGrid_endpoint_error_spread_gt_of_output_spread`
- `ieeeDoubleKahanRationalFunction_endpoint_error_spread_gt_of_output_spread`
- `kahanRationalFunction_grid_175_289_variation_lt_one_e15`
- `kahanRoundedGrid_175_289_error_spread_gt_of_output_spread`
- `ieeeDoubleKahanRationalFunction_175_289_error_spread_gt_of_output_spread`
- `ieeeDoubleKahanStoredGridPoint`
- `ieeeDoubleKahanStoredGridRationalFunction`
- `ieeeDoubleKahanStoredGridPoint_175_eq`
- `ieeeDoubleKahanStoredGridPoint_289_eq`
- `ieeeDoubleKahanStoredGridNumerator_m0_175_eq`
- `ieeeDoubleKahanStoredGridNumerator_m0_289_eq`
- `ieeeDoubleKahanStoredGridNumerator_s0_175_eq`
- `ieeeDoubleKahanStoredGridNumerator_s0_289_eq`
- `ieeeDoubleKahanStoredGridNumerator_m1_175_eq`
- `ieeeDoubleKahanStoredGridNumerator_m1_289_eq`
- `ieeeDoubleKahanStoredGridNumerator_s1_175_eq`
- `ieeeDoubleKahanStoredGridNumerator_s1_289_eq`
- `ieeeDoubleKahanStoredGridNumerator_m2_175_eq`
- `ieeeDoubleKahanStoredGridNumerator_m2_289_eq`
- `ieeeDoubleKahanStoredGridNumerator_s2_175_eq`
- `ieeeDoubleKahanStoredGridNumerator_s2_289_eq`
- `ieeeDoubleKahanStoredGridNumerator_m3_175_eq`
- `ieeeDoubleKahanStoredGridNumerator_m3_289_eq`
- `ieeeDoubleKahanStoredGridHornerNumerator_175_eq`
- `ieeeDoubleKahanStoredGridHornerNumerator_289_eq`
- `ieeeDoubleKahanStoredGridDenominator_s0_175_eq`
- `ieeeDoubleKahanStoredGridDenominator_s0_289_eq`
- `ieeeDoubleKahanStoredGridDenominator_m1_175_eq`
- `ieeeDoubleKahanStoredGridDenominator_m1_289_eq`
- `ieeeDoubleKahanStoredGridDenominator_s1_175_eq`
- `ieeeDoubleKahanStoredGridDenominator_s1_289_eq`
- `ieeeDoubleKahanStoredGridDenominator_m2_175_eq`
- `ieeeDoubleKahanStoredGridDenominator_m2_289_eq`
- `ieeeDoubleKahanStoredGridDenominator_s2_175_eq`
- `ieeeDoubleKahanStoredGridDenominator_s2_289_eq`
- `ieeeDoubleKahanStoredGridDenominator_m3_175_eq`
- `ieeeDoubleKahanStoredGridDenominator_m3_289_eq`
- `ieeeDoubleKahanStoredGridHornerDenominator_175_eq`
- `ieeeDoubleKahanStoredGridHornerDenominator_289_eq`
- `ieeeDoubleKahanStoredGridRationalFunction_175_eq`
- `ieeeDoubleKahanStoredGridRationalFunction_289_eq`
- `ieeeDoubleKahanStoredGridRationalFunction_175_289_error_spread_gt_of_output_spread`
- `ieeeDoubleKahanStoredGridRationalFunction_175_289_error_spread_gt_one_e13_of_output_values`
- `ieeeDoubleKahanStoredGridRationalFunction_175_289_error_spread_gt_one_e13`
- `exists_ieeeDoubleKahanStoredGridRationalFunction_grid_error_spread_gt_one_e13`
- `ieeeDoubleKahanStoredGridError`
- `exists_ieeeDoubleKahanStoredGridError_pair_spread_gt_one_e13`
- `not_forall_ieeeDoubleKahanStoredGridError_eq_on_source_grid`
- `flKahanHornerNumerator_eq_errorEval`
- `flKahanHornerDenominator_eq_errorEval`
- `flKahanRationalFunction_eq_errorEval`
- `ieeeDoubleKahanHornerNumerator_eq_errorEval_of_finiteNormal`
- `ieeeDoubleKahanHornerDenominator_eq_errorEval_of_finiteNormal`
- `ieeeDoubleKahanRationalFunction_eq_errorEval_of_finiteNormal`

Existing Lean surface still relevant:

- `BasicOp`, `BasicOp.exact`, `FPModel.round`, `FPModel.model_basicOp`
- `absError`, `relError`, `relErrorComputedDenom`, `relErrorDefined`,
  `signedRelErrorWitness`
- `relError_smul`, `relError_eq_abs_of_signedRelErrorWitness`
- `exists_signedRelErrorWitness_of_relErrorDefined`
- `normwiseRelError`, `compRelError`, `compRelErrorBounded`
- `ErrorSource`, `ErrorSource.chapterOneMainSource_exhaustive`
- `AccuracyMeasure`, `AccuracyMeasure.value`
- `AccuracyMeasure.value_absolute`, `AccuracyMeasure.value_relative`
- `PrecisionMeasure`, `PrecisionMeasure.ofFPModel`
- `PrecisionMeasure.ofFPModel_unitRoundoff`
- `SimulatesHigherPrecision`
- `BasicOperationPrecisionBounded`
- `FPModel.basicOperationPrecisionBounded`
- `fl_mul_accuracy_witness_of_precision`
- `fl_mul_relError_le_precision`
- `backwardErrorBounded`, `backwardErrorBoundedVec`
- `relBackwardErrorBounded2`, `isRelComponentwiseBackwardStable`
- `condNumber`, `isWellConditioned`, `forward_from_backward`
- later-file QR facts such as `GivensQRBackwardError`/Theorem 18.9 surfaces
  are relevant to the QR example, but they do not by themselves close the
  Chapter 1 worked example.

## Line-By-Line Result Audit

Line references are from `/private/tmp/chapter01_full_layout.txt`.  Prose,
history, epigraphs, and advice are classified separately from theorem/algorithm
obligations.

| Extracted lines | Source content | Formalization status |
|---|---|---|
| 1--66 | Chapter title, epigraphs, scope, and assumptions. | Prose-only; no theorem obligation. |
| 67--141 | §1.1 notation/background; equation (1.1) for primitive floating-point operations; unit roundoff. | Closed by `BasicOp`, `BasicOp.exact`, `FPModel.round`, `FPModel.model_basicOp`. |
| 142--267 | §1.2 scalar absolute/relative error, signed relative-error form, scale invariance, normwise and componentwise vector relative error, significant-digit discussion. | Mathematical definitions closed by `absError`, `relError`, `signedRelErrorWitness`, `relError_smul`, `normwiseRelError`, `compRelError`. Significant-digit discussion remains explanatory because the source itself warns that exact digit-count definitions are problematic. |
| 268--279 | §1.3 three main error sources: rounding, data uncertainty, truncation. | Closed by `ErrorSource` and `ErrorSource.chapterOneMainSource_exhaustive`. |
| 280--298 | §1.4 precision versus accuracy. | Closed at the vocabulary layer by `AccuracyMeasure`, `AccuracyMeasure.value`, `PrecisionMeasure`, `PrecisionMeasure.ofFPModel`, `BasicOperationPrecisionBounded`, and `FPModel.basicOperationPrecisionBounded`: accuracy is represented by absolute or relative error, while precision is the unit roundoff controlling the basic arithmetic operations. The scalar multiplication statement is closed by `fl_mul_accuracy_witness_of_precision` and `fl_mul_relError_le_precision`, showing that a rounded `a*b` has signed relative accuracy bounded by the model precision when the exact product is nonzero. The higher-precision-simulation caveat is recorded by `SimulatesHigherPrecision`; no concrete simulation algorithm is claimed in Chapter 1. |
| 299--372 | §1.5 backward error, forward error, backward stability, mixed forward-backward stability, numerical stability. | Foundational vocabulary closed by `backwardErrorBounded`, `forwardErrorBounded`, `mixedForwardBackwardErrorBounded`, `isBackwardStable`, `isNumericallyStable`, and vector analogues. Concrete algorithm instantiations are open where the chapter later gives examples. |
| 373--423 | §1.6 conditioning, scalar condition number, rule of thumb forward error is governed by conditioning times backward error, forward stability relative to backward-stable methods. | Partly closed by `condNumber`, `isWellConditioned`, `forward_from_backward`, and `isForwardStableRelativeTo` for scalar problems. The finite-vector normwise condition-number-bound surface and rule of thumb are closed by `normwiseBackwardErrorBoundedVec`, `normwiseConditionNumberBoundedVec`, and `normwise_forward_from_backward_vec`, which prove `forwardErrorBoundedVec <= κ * (ε / ||a||_in)` from a normwise backward-error witness and a local condition-number bound on the same perturbation radius. The source-facing maximum/supremum language is now represented by `normwiseConditionNumberSupremumVec`, `normwiseConditionNumberAttainedVec`, `normwiseConditionNumberSupremumVec_of_attained_bound`, and `normwise_forward_from_backward_vec_of_condition_supremum`; concrete compactness/attainment proofs remain only for later chosen norms or domains, not as a Chapter 1 generic blocker. |
| 424--474 | §1.7 cancellation; subtraction of perturbed quantities; cancellation in `1 - cos x` and stable rewrite `2 sin^2(x/2)`. | Perturbed-subtraction algebra closed by `subtract_perturbed_error_eq`, `abs_subtract_perturbed_error_le`, and `relError_subtract_perturbed_le_eps_amp`. Exact trig rewrite and the source scaled-target range are closed by `one_sub_cos_eq_two_sin_sq_half`, `one_sub_cos_nonneg_exact`, `trigCancellationExactScaled_nonneg`, `trigCancellationExactScaled_le_half`, `trigCancellationExactScaled_lt_half`, and `trigCancellationExactScaled_pos_of_cos_ne_one`: the scaled target is nonnegative, at most `1/2`, strictly below `1/2` for `x != 0`, and strictly positive when `cos x != 1`. Supplied trigonometric approximation error propagation is closed by `trigCancellationDirectScaledFromCos_abs_error_le`, `sq_abs_error_le_of_abs_sub_le`, `trigCancellationRewriteScaledFromSinHalf_abs_error_le`, and `trigCancellationRewriteScaledFromSinHalf_abs_error_le_direct_cos_bound`: direct cosine error is divided by `x^2`, while the half-angle path is controlled by the sine-half input error and has an explicit comparison criterion against a direct cosine-error budget. The finite round-to-even trigonometric-output wrapper is closed by `trigCancellationFiniteRoundToEvenCos_abs_error_le`, `trigCancellationFiniteRoundToEvenSinHalf_abs_error_le`, `trigCancellationDirectScaledFiniteRoundToEvenCos_abs_error_le`, `trigCancellationRewriteScaledFiniteRoundToEvenSinHalf_abs_error_le`, and `trigCancellationRewriteScaledFiniteRoundToEvenSinHalf_abs_error_le_direct_cos_bound`: under finite-normal hypotheses for `cos x` and `sin(x/2)`, the total finite round-to-even selector supplies the exact `eta` budgets consumed by the downstream scaled-error theorems. The displayed ten-significant-figure example is formalized as exact rational arithmetic by `trigCancellationDirectScaled_eq`, `trigCancellationDirectScaled_ne_half`, and `trigCancellationRewriteScaled_eq_half`: the direct scaled value is `25/36`, not `1/2`, while the rewritten scaled value is exactly `1/2`. Remaining implementation gap: instantiate full named libm/IEEE-library sine/cosine routines beyond this ideal finite round-to-even output selector, if those routines are required. |
| 475--519 | §1.8 solving a quadratic equation; standard formula (1.3), cancellation in one root, stable root recovery via the product relation, overflow/underflow caveats. | Exact algebra closed by `quadraticRootPlus_is_root`, `quadraticRootMinus_is_root`, `quadratic_roots_product`, and `quadraticRootMinus_eq_c_div_a_mul_rootPlus`/`quadraticRootPlus_eq_c_div_a_mul_rootMinus`. The exact branch-choice and direct cancellation comparison are closed by `quadraticRootMinusNumerator_abs_eq_abs_b_add_s_of_b_nonneg`, `quadraticRootPlusNumerator_abs_eq_abs_b_add_s_of_b_nonpos`, `quadraticRootPlusNumerator_abs_le_of_b_nonneg_s_close`, `quadraticRootMinusNumerator_abs_le_of_b_nonpos_s_close`, `quadraticRootPlus_abs_le_rootMinus_of_b_nonneg`, `quadraticRootMinus_abs_le_rootPlus_of_b_nonpos`, and `quadraticRootSmallByBSign_abs_le_largeByBSign`: the sign-of-`b` selector chooses the larger-magnitude exact branch, and the opposite numerator is small when the square-root input is close to `|b|`. The rounded discriminant operation trace and named absolute-error radius are closed by `flQuadraticDiscriminant_expansion`, `flQuadraticDiscriminantAbsErrorBound`, `flQuadraticDiscriminant_abs_error_le`, and `flQuadraticDiscriminant_abs_error_le_bound`; `flQuadraticDiscriminant_nonneg_of_abs_error_bound_le` proves the rounded discriminant is nonnegative whenever the exact discriminant dominates that radius. The higher-precision discriminant layer is now closed at the abstract `FPModel` level by `flQuadraticDiscriminantAbsErrorBound_eq_poly`, `flQuadraticDiscriminantAbsErrorBound_le_of_u_le`, `flQuadraticDiscriminantAbsErrorBound_le_of_simulatesHigherPrecision`, `flQuadraticRootPlusMixedDiscriminantSqrt_abs_error_le`, and `flQuadraticRootMinusMixedDiscriminantSqrt_abs_error_le`: if the discriminant arithmetic has smaller unit roundoff and its discriminant radius separates the exact discriminant from zero, the mixed path using that discriminant and root-precision square root/branch arithmetic has an explicit root error bound. The small-discriminant/nearly-equal-root cluster case is closed at the exact certificate layer by `quadraticRootPlus_sub_midpoint_abs_eq`, `quadraticRootMinus_sub_midpoint_abs_eq`, `quadraticRootSeparation_abs_eq`, `quadraticRoots_near_midpoint_of_discriminant_le`, and `quadraticRoots_near_midpoint_of_discriminant_guard_failure`: if the separation guard fails, real roots are certified to lie within `sqrt(flQuadraticDiscriminantAbsErrorBound fp a b c)/(2*|a|)` of `-b/(2*a)`, with mutual separation at most `sqrt(flQuadraticDiscriminantAbsErrorBound fp a b c)/|a|`. The rounded standard-formula branch micro-kernel with a supplied square-root value is closed by `flQuadraticRootPlusFromSqrt_rel_error_le_gamma3` and `flQuadraticRootMinusFromSqrt_rel_error_le_gamma3`, proving `fl(fl(-b ± s) / fl(2*a)) = x_±*(1+theta)` with `|theta| <= gamma_3` when `a != 0` and `gammaValid fp 3`. The supplied relative-error, absolute-error, and discriminant-error square-root input bridges are closed by the `quadraticRoot*_sqrt_*` lemmas, `flQuadraticRoot*WithSqrtRelError_abs_error_le`, `flQuadraticRoot*FromSqrt_abs_input_error_le`, and `flQuadraticRoot*FromSqrt_discriminant_abs_error_le`. The concrete rounded-discriminant/square-root branch path is closed conditionally by `flQuadraticRootPlusRoundedDiscriminantSqrt_abs_error_le` and `flQuadraticRootMinusRoundedDiscriminantSqrt_abs_error_le`: under `flQuadraticDiscriminantAbsErrorBound fp a b c <= quadraticDiscriminant a b c`, the branches using `fp.fl_sqrt (flQuadraticDiscriminant fp a b c)` have an explicit absolute-error bound around the exact roots using `Real.sqrt (quadraticDiscriminant a b c)`. The exact-discriminant computed-square-root branch remains closed by `flQuadraticRootPlusComputedSqrt_abs_error_le` and `flQuadraticRootMinusComputedSqrt_abs_error_le`. The rounded product-recovery micro-kernel is closed by `flQuadraticRecoveredRootFromOther_rel_error_le_gamma2`, proving `fl(c / fl(a*xhat)) = c/(a*xhat)*(1+theta)` with `|theta| <= gamma_2` when `a*xhat != 0` and `gammaValid fp 2`. The supplied-root accuracy composition is now closed by `flQuadraticRecoveredRootFromOther_abs_error_le_of_abs_error`, `flQuadraticRecoveredRootMinusFromPlus_abs_error_le`, and `flQuadraticRecoveredRootPlusFromMinus_abs_error_le`: if `|xhat-x| <= eta < |x|`, product recovery has an explicit absolute-error bound around the companion root. The concrete rounded-discriminant branch-to-recovery endpoints are closed by `flQuadraticRecoveredRootMinusFromRoundedPlusDiscriminantSqrt_abs_error_le` and `flQuadraticRecoveredRootPlusFromRoundedMinusDiscriminantSqrt_abs_error_le`, assuming the discriminant separation guard and that the named branch error radius is smaller than the exact branch root magnitude. The total sign-of-`b` rounded pair is closed conditionally by `flQuadraticRootLargeByBSignRoundedDiscriminantSqrt_abs_error_le`, `flQuadraticRootSmallByBSignRoundedDiscriminantSqrt_abs_error_le`, and `flQuadraticRootsByBSignRoundedDiscriminantSqrt_abs_error_le`: it computes the larger branch selected by `b`'s sign and recovers the companion root, under the same discriminant separation guard plus the branch-radius-smaller-than-root guard. The concrete IEEE range substrate for the displayed overflow example is closed by `quadraticOverflowExample_b_square_single_finiteOverflowRange`, `quadraticOverflowExample_b_square_double_finiteNormalRange`, `quadraticOverflowExample_four_ac_double_finiteNormalRange`, `quadraticOverflowExample_discriminant_double_finiteNormalRange`, `quadraticOverflowExample_discriminant_path_double_finiteNormalRange`, `quadraticOverflowExample_scaled_b_square_single_finiteNormalRange`, `quadraticOverflowExample_scaled_four_ac_single_finiteNormalRange`, and `quadraticOverflowExample_scaled_discriminant_single_finiteNormalRange`: the unscaled formula path has `b*b` outside the single finite range, the same unscaled `b*b`, `4*a*c`, and exact discriminant intermediates are normal-range in IEEE double finite-format range, and the divided equation has the `b*b`, `4*a*c`, and discriminant intermediates in the single normal finite range. The exact overflow/scaling examples are closed by `quadraticOverflowExample_roots`, `quadraticScaledOverflowExample_roots`, and `quadraticScaledOverflowExample_variable_scaling`: the first displayed `10^20` equation has roots `1` and `2`, the second has roots `10^20` and `2*10^20`, and the substitution `x = 10^20*y` transforms the second equation into the first. Closed additionally: the actual rounded-intermediate IEEE double trace is normal-range, nearest/even standard-model, no-flag, and value-field linked by the `quadraticOverflowExample_*doubleRounded*` theorems. Closed additionally: the displayed twice-precision operation trace is instantiated by `quadraticOverflowExample_singleOverflow_doubleRoundedDiscriminantTrace`; the reusable finite-normal no-flag/value-field guard is closed in `FloatingPointArithmetic.lean`, while full IEEE special-value/trap semantics remain beyond these displayed finite-range examples. |
  §1.8 twice-precision addendum:
  `quadraticOverflowExample_singleOverflow_doubleRoundedDiscriminantTrace`
  bundles the displayed single-overflow fact with the actual IEEE-double
  rounded-intermediate discriminant trace: the single `b*b` primitive is outside
  the IEEE-single finite range, while the double trace has normal-range exact
  primitive results, no exception flags, and value fields equal to the named
  finite round-to-even trace values.  This closes the displayed finite
  double/twice-precision operation trace; remaining IEEE scope is full
  special-value/trap semantics outside this finite example path.
  Audit correction: the older "Open: instantiate twice-precision operation
  traces" phrase in the long §1.8 row above is superseded by this wrapper and
  by the C1F.3 addendum in the not-proved ledger.
| 520--583 | §1.9 computing sample variance; formulas (1.4), (1.5), and update recurrences (1.6a,b); one-pass instability; two-pass/Welford-style stability discussion. | Closed at theorem level by `SampleVariance.lean`: `sampleMean`, `sampleVarianceTwoPass`, `sampleVarianceTwoPassWithMean`, `sampleVarianceOnePass`, `sampleVarianceTwoPass_eq_onePass`, `sampleVarianceShiftedOnePass_eq_twoPass`, `sampleVarianceTwoPass_nonneg`, `sampleVarianceOnePass_nonneg_exact`, `prefixMean_succ`, `prefixCorrectedSumSquares_succ`, `prefixMean_example_values_10000_10001_10002`, `prefixCorrectedSumSquares_example_values_10000_10001_10002`, `sampleVarianceUpdate_example_10000_10001_10002`, and `sampleVarianceTwoPass_example_10000_10001_10002`. The exact update-recursion example proves `M_1=10000`, `M_2=20001/2`, `M_3=10001`, `Q_1=0`, `Q_2=1/2`, `Q_3=2`, hence `Q_3/(3-1)=1` for `[10000,10001,10002]`. The rounded one-step update recurrences are closed locally by `flPrefixMeanStep_eq_exact_with_local_errors`, `flPrefixMeanStep_abs_error_le`, `flPrefixMeanStep_abs_error_le_prefixMean_succ`, `flPrefixCorrectedSumSquaresStep_eq_exact_with_local_errors`, `flPrefixCorrectedSumSquaresStep_abs_error_le`, and `flPrefixCorrectedSumSquaresStep_abs_error_le_prefix_succ`: the mean update has a two-operation relative factor on the correction plus a final rounded-add factor, and the corrected-sum-of-squares update has a five-operation relative factor on the new term plus a final rounded-add factor. The full rounded update trajectories are now composed by `flPrefixMeanTrajectory_abs_error_le_budget` and `flPrefixCorrectedSumSquaresTrajectory_abs_error_le_budget`; their nonnegative recursive budgets are proved by `flPrefixMeanTrajectoryAbsErrorBudget_nonneg` and `flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget_nonneg`, with `prefixCorrectedSumSquaresStepExact_abs_sub_le` propagating rounded mean error into the `Q_k` update. The final quotient is closed by `flSampleVarianceUpdate_abs_error_le_budget`, with nonnegative bound `flSampleVarianceUpdateAbsErrorBudget_nonneg`, proving the rounded update algorithm's result is within the recursive `Q_n` budget divided by `|n-1|` plus one final division-rounding term for `n > 1`. The aggregate one-pass warning is closed by `sampleVarianceOnePassAggregates_exact_example_10000_10001_10002`, `sampleVarianceOnePassAggregates_cancelled_example_10000_10001_10002`, `sampleVarianceOnePassAggregates_cancelled_relError_example_10000_10001_10002`, `sampleVarianceOnePassAggregates_neg_of_sumSq_lt`, `sampleVarianceOnePassAggregates_negative_example_10000_10001_10002`, `sampleVarianceOnePassAggregates_negative_lt_zero_example_10000_10001_10002`, `sampleVarianceOnePassAggregates_negative_absError_example_10000_10001_10002`, and `sampleVarianceOnePassAggregates_negative_relError_example_10000_10001_10002`: exact aggregates give variance `1`, the collapsed pair `(300060003,30003)` gives `0` and relative error `1`, and the neighboring pair `(300060002,30003)` gives `-1/2`, is strictly negative, and has absolute and relative error `3/2` against the exact variance. The concrete binary32 one-pass operation trace is closed by `sampleVarianceOnePassIeeeSingleRoundingCertificate`, `sampleVarianceOnePassIeeeSingle_sourceRoundingEvidenceCertificate`, `sampleVarianceOnePassIeeeSingle_sq0_eq`, `sampleVarianceOnePassIeeeSingle_sq1_eq`, `sampleVarianceOnePassIeeeSingle_sq2_eq`, `sampleVarianceOnePassIeeeSingle_sum01_eq`, `sampleVarianceOnePassIeeeSingle_sum_eq`, `sampleVarianceOnePassIeeeSingle_sumSq_eq`, `sampleVarianceOnePassIeeeSingle_sumSquare_eq`, `sampleVarianceOnePassIeeeSingle_meanSquareTerm_eq`, `sampleVarianceOnePassIeeeSingleRoundingCertificate_closed`, `sampleVarianceOnePassIeeeSingleTrace_zero`, and `sampleVarianceOnePassIeeeSingleTrace_relError_one`: Lean proves the grid-point operations exactly, proves source round-to-even evidence for the four non-grid primitive roundings `10001^2 -> 100020000`, `10002^2 -> 100040000`, `30003^2 -> 900180032`, and `900180032/3 -> 300060000`, proves total-selector equalities for all four non-grid primitive roundings including the halfway/even `10002^2` case, and proves the rounded operation trace returns `0.0` with relative error `1` against the exact two-pass variance. Problem 1.7's closed-form sample-variance condition-number derivation is closed by `sampleMean_add_scaled`, `sampleVarianceTwoPass_add_scaled_sub_eq`, `sampleVarianceDirectionalCoeff_componentwise_le`, `sampleVarianceDirectionalCoeff_normwise_le`, `sampleVariance_vecNorm2Sq_eq_conditionDen_add_mean_sq`, `sampleVarianceKappaNClosed_eq_expanded`, `sampleVarianceKappaCClosed_le_KappaNClosed`, `sampleVarianceProblem17RelativeRemainderCoeff`, `sampleVarianceProblem17RelativeRemainderEnvelope`, `sampleVarianceTwoPass_relative_add_scaled_sub_linear_eq_remainder`, and `sampleVarianceProblem17RelativeRemainderEnvelope_isBigO`. Problem 1.10's exact perturbed-mean substrate and rounded two-pass transfer are closed through `sampleMean_deviation_sum_eq_zero`, `sum_sq_sub_perturbedMean_eq_sum_sq_sub_sampleMean_add`, `sampleVarianceTwoPassWithMean_eq_twoPass_add`, `sampleVarianceTwoPass_le_twoPassWithMean`, `sampleVarianceTwoPassWithMean_relError_eq_quadratic`, `sampleVarianceTwoPassWithMean_mul_one_add_relError_le`, `flSampleMean_backward_error`, `flSampleMean_abs_error_le_gamma`, `flSampleVarianceTwoPassWithMean_eq_mul_one_add_gamma`, `flSampleVarianceTwoPass_relError_le_gamma_add_mean_quadratic`, `flSampleVarianceTwoPass_mean_quadratic_le_gamma_sq`, `flSampleVarianceTwoPass_relError_le_gamma_add_gamma_sq_mean_bound`, `gamma_eq_linear_plus_quadratic_remainder`, and `flSampleVarianceTwoPass_relError_le_linear_u_add_explicit_remainder`, giving the source linear term `(n+3)u` plus an explicit higher-order remainder. The source-level negative-output statement is closed: Lean proves the general aggregate criterion for negativity and a finite binary32 supplied-aggregate final trace; upstream accumulation to that negative aggregate is optional implementation provenance because the PDF gives no concrete negative-output dataset or machine trace. The literal Problem 1.7 `O(t^2)` and Problem 1.10 `O(u^2)` quadratic-remainder wrappers are closed by the theorem names listed below. |
  Sample-variance supplied-negative final-trace update:
  `sampleVarianceOnePassIeeeSingleNegativeAggregate_inputs_finiteSystem`,
  `sampleVarianceOnePassIeeeSingleNegativeAggregate_numerator_eq`,
  `sampleVarianceOnePassIeeeSingleNegativeAggregateTrace_eq_neg_sixteen`,
  `sampleVarianceOnePassIeeeSingleNegativeAggregateTrace_lt_zero`, and
  `sampleVarianceOnePassIeeeSingleNegativeAggregateTrace_relError` now prove a
  concrete binary32 finite final-operation diagnostic: supplied rounded
  aggregates `300059968` and `300060000` subtract exactly to `-32`, divide
  exactly to `-16`, are strictly negative, and have relative error `17` against
  the exact variance `1`. This does not contradict the concrete
  `[10000,10001,10002]` binary32 trace above, which Lean proves returns `0`;
  upstream accumulation to this supplied negative aggregate pair is optional
  implementation provenance, not a theorem-level obligation.

  Problem 1.10 quadratic-envelope update: `flSampleVarianceTwoPassProblem110RemainderQuadraticBound`,
  `flSampleVarianceTwoPassProblem110RemainderQuadraticCoeff`,
  `flSampleVarianceTwoPassProblem110RemainderQuadraticBound_eq_coeff_mul_u_sq`,
  `flSampleVarianceTwoPassProblem110RemainderQuadraticEnvelope`,
  `flSampleVarianceTwoPassProblem110RemainderQuadraticEnvelope_eq_bound`,
  `flSampleVarianceTwoPassProblem110RemainderQuadraticEnvelope_isBigO`, and
  `flSampleVarianceTwoPassProblem110Remainder_le_quadratic_bound` now prove
  that the named higher-order remainder after the source linear term `(n+3)u`
  is bounded by an explicit expression that is literally a fixed
  data-dependent coefficient times `u^2` when `(n+3)u <= 1/2`, `n > 1`, and the
  exact two-pass variance is positive. The scalar envelope is also proved in
  mathlib Landau notation as `O(u^2)` along `u -> 0`.
| 584--628 | §1.10 solving linear equations; residual, relative residual, normwise backward error for perturbing `A`, and Lemma 1.1. | Closed in predicate form by `higham_lemma_1_1_operator2_predicate` and `higham_lemma_1_1_relativeResidual2_predicate`. The repository represents `||Delta A||_2 <= c` by `opNorm2Le`; `matrixNormA > 0` is supplied as the value of `||A||_2` for the relative statement. |
| 629--695 | §1.10.1 GEPP versus Cramer's rule; 2-by-2 example and forward/backward-stability contrast. | Partly closed exactly by `CramersRule.lean`: `det2x2`, `cramer2x2X1`, `cramer2x2X2`, `cramer2x2_first_eq`, `cramer2x2_second_eq`, and `cramer2x2Solution_solves` formalize the 2-by-2 Cramer formula and prove it solves the exact system when the determinant is nonzero. The explicit inverse is closed by `cramer2x2Inverse_isInverse`. The Problem 1.9 denominator-exact rounded-numerator bridge is closed by `flDet2x2_error_le_gamma3`, `flCramer2x2Numerator_error_le_gamma3`, and `cramer2x2Solution_error_from_flNumerators_exact_den`; the forward condition-number form `||xhat-x||∞/||x||∞ <= gamma_3 * cond(A,x)` is closed by `cramer2x2Solution_relative_forward_error_from_flNumerators_exact_den_condAt`, with `cond(A,x)` represented by `cramer2x2CondAt`; and the residual condition-number form `||b-A*xhat||∞ <= gamma_3 * cond(A^{-1}) * ||b||∞` is closed by `cramer2x2Residual_infNorm_from_flNumerators_exact_den_condInv`, with `cond(A^{-1})` represented by `cramer2x2ResidualCond`. The rounded-exact-solution residual comparison is closed in predicate form by `residualVec_add_error_eq_neg_matMulVec`, `residual_norm_add_error_eq_matMulVec_norm`, `roundedExactSolution_residual_norm_le_opNorm2_mul_relative_error`, `relativeResidual2`, and `roundedExactSolution_relativeResidual2_le_relative_error_factor`. The 2-by-2 GEPP/LU scaled-residual bridge is closed by `gepp2_relativeResidual2_le_wilkinson`, which proves `relativeResidual2 <= sqrt(2) * gamma_6 * 2 * ||U_hat||∞ / ||A||₂` from the local LU backward-error theorem, nonzero triangular diagonals, `gammaValid fp 2`, `gammaValid fp 6`, and the partial-pivoting multiplier bound `|L_hat i j| <= 1`. Visual audit of the PDF page shows the table column is `r/(||A||₂||xhat||₂)`, so the displayed MATLAB solution/scaled-residual rows are closed as exact rational data by `cramerGeppExample_cramerSolution_rows`, `cramerGeppExample_cramerScaledResidual_rows`, `cramerGeppExample_geppSolution_rows`, `cramerGeppExample_geppScaledResidual_rows`, and `cramerGeppExample_accurateVector_rows`; the older `...Residual...` names are compatibility aliases for this printed scaled-residual column, not raw residual data. `cramerGeppExample_scaledResidual_component_gap` proves each printed Cramer scaled-residual component is more than `10^9` times the corresponding printed GEPP scaled-residual component in absolute value. The printed scaled-residual norm layer is closed by `cramerGeppExample_cramerScaledResidual_infNorm_eq`, `cramerGeppExample_geppScaledResidual_infNorm_eq`, `cramerGeppExample_scaledResidual_infNorm_gap`, `cramerGeppExample_cramerScaledResidual_vecNorm2Sq_eq`, `cramerGeppExample_geppScaledResidual_vecNorm2Sq_eq`, and `cramerGeppExample_scaledResidual_vecNorm2Sq_gap`: the Cramer printed scaled-residual norm is more than `10^9` times the GEPP one. Open: reconstruct the hidden MATLAB matrix/RHS, exact solution, and `K_2(A)` provenance if that generation path is required; the raw residual vector is not printed and should not be inferred from the scaled column without the hidden norm scale. |
| 696--726 | §1.11 accumulation of rounding errors; `(1 + 1/n)^n`, Strassen example, and asymptotic warning. | Partly closed by `expOneApproxRoundedBase_eq_exact_base_mul_initial_error_pow`, which proves that if only the initial base `1 + 1/n` is rounded and subsequent exponentiation is exact, the result is the exact finite-`n` approximation multiplied by `(1+delta)^n` for some `|delta| <= u`. The displayed finite data in Table 1.1 is now closed by `expOneApproxTable11_n_rows`, `expOneApproxTable11_computed_rows`, and `expOneApproxTable11_relativeError_rows`, which encode the seven `n`, computed-approximation, and relative-error entries as exact rationals; `expOneApproxTable11_tail_relativeError_strictly_increases` and `expOneApproxTable11_last_two_relativeError_gt_one_tenth` prove the source's displayed large-`n` degradation/poor-tail observation directly from those rows. The source's sentence that `1/n` has a nonterminating binary expansion when `n` is a power of ten is closed by `one_div_ten_pow_succ_not_binaryTerminating`, which proves `1/10^(k+1)` is not a terminating binary fraction for every `k`. The Strassen dominant leaf-multiplication count substrate is closed by `strassenThresholdHalving_same_dimension_and_decreases_count`: for the same represented matrix dimension, halving the classical leaf threshold and adding one recursion level strictly reduces the dominant leaf multiplication count. The exact/log-error core and supplied rounded-outer-exp composition layer of Problem 1.5 are closed by `expOneApproxLogExpExact_eq_exact_base`, `expOneApproxLogExpWithLogRelError_eq_exact_base_mul_exp`, `expOneApproxLogExp_exponentCoeff_nonneg`, `expOneApproxLogExp_exponentCoeff_le_one`, `expOneApproxLogExp_logRelError_exponent_abs_le`, `expOneApproxLogExpRoundedOuter_eq_exact_base_mul_exp_mul`, `real_abs_exp_sub_one_le_of_abs_le`, `expOneApproxLogExpRoundedOuter_relError_le_exp_mul`, and `expOneApproxLogExpRoundedOuter_relError_le_fp`: a relative log error `|epsLog| <= u` induces an exponent perturbation with absolute value at most `u`, and adding a supplied final exponential relative-error factor `|epsExp| <= u` gives relative error at most `exp(u)*(1+u)-1`. The scalar envelope's literal first-order form is closed by `expOneApproxLogExpUnitRoundoffEnvelope_isBigO`, proving `exp(u)*(1+u)-1 = O(u)` as `u -> 0`. The finite round-to-even wrapper `expOneApproxLogExpFiniteRoundToEven_relError_le_fp_of_finiteNormalRange` now instantiates those supplied `epsLog`/`epsExp` variables from finite-normal `FloatingPointFormat.finiteRoundToEven` outputs for the logarithm and outer exponential. Open: a concrete Fortran execution derivation of the Table 1.1 values, full named libm/IEEE exp/log implementation contracts beyond the finite round-to-even selector, and Strassen's empirical threshold-error growth beyond the dominant multiplication-count substrate. |
| 696--726 addendum | §1.11 single-rounded-base relative-error formula. | Closed by `expOneApproxRoundedBase_relError_eq_initial_error_pow_abs`: under the same model in which only the base `1 + 1/n` is rounded and the subsequent exponentiation is exact, Lean proves there is a `delta` with `|delta| <= fp.u` such that the relative error is exactly `|(1+delta)^n - 1|`. This is the source's amplification mechanism stated as one theorem over all `n`, not an enumeration of Table 1.1 cases and not a hidden Fortran or named power-routine derivation. |
| 696--726 addendum | §1.11 exact finite-`n` convergence baseline. | Closed by `expOneApproxExactBase_tendsto_exp_one`: Lean proves the exact real sequence `(1+1/n)^n` tends to `exp(1)`. This records the mathematical baseline behind the table before any rounding-error accumulation is introduced; it does not reconstruct the hidden Fortran execution path for the displayed table entries. |
| 727--825 | §1.12 instability without cancellation; pivoting example, innocuous square-root/squaring calculation, infinite sum. | Partly closed. The §1.12.1 no-pivot LU example is closed at the exact/modelled-rounding level by `noPivotExampleAInv_isInverse`, `noPivotExample_kappaInf_eq`, `noPivotRoundedLU_error_matrix`, and `noPivotRoundedLU_not_reproduce_A`: for `0 < ε <= 1`, the displayed inverse is valid, `||A||∞ ||A^{-1}||∞ = 4/(1+ε)`, and if the no-pivot update rounds `fl(1+ε^{-1})` to `ε^{-1}`, then `A - Lhat*Uhat = [[0,0],[0,1]]`. The concrete IEEE-single sufficiently-small instance is closed by `noPivotIeeeSingle_add_one_inv_epsilon_rounds_to_inv`: for `ε = 2^{-24}`, nearest/even single precision gives `fl(1+ε^{-1}) = ε^{-1}`; `noPivotIeeeSingleSmallEpsilon_error_matrix` specializes the displayed reproduction failure to that ε. The exact partial-pivoting branch for the same example is closed by `noPivotPartialPivotLUFactSpec`, `noPivotPartialPivot_multiplier_abs_le_one`, `noPivotPartialPivotU_diag_nonzero`, and `noPivotPartialPivotLUBackwardError_zero`: the row interchange gives `P*A=L*U`, the multiplier satisfies `|ε| <= 1` under `0 <= ε <= 1`, the pivoted `U` has nonzero diagonal entries under `0 <= ε`, and the exact pivoted factors satisfy `PermutedLUBackwardError` with zero perturbation. The concrete IEEE-single pivoted primitive trace at `ε = 2^{-24}` is closed by `noPivotIeeeSingleSmallEpsilon_finiteSystem`, `noPivotIeeeSingle_partialPivot_div_epsilon_one_rounds_to_epsilon`, `noPivotIeeeSingle_partialPivot_mul_epsilon_one_rounds_to_epsilon`, `noPivotIeeeSingle_add_one_epsilon_rounds_to_one`, and `noPivotIeeeSingle_partialPivot_sub_neg_one_epsilon_rounds_to_neg_one`: Lean proves `ε` is representable, `fl(ε/1)=ε`, `fl(ε*1)=ε`, `fl(1+ε)=1`, and the signed update `fl((-1)-ε)=-1`. The rounded pivoted factors use `noPivotPartialPivotIeeeSingleRoundedU` with `U_22=-1`, and `noPivotIeeeSinglePartialPivotRoundedLUBackwardError` proves their componentwise pivoted LU backward-error certificate with radius `ε`. The generic supplied-operation pivoted bridge is closed by `noPivotPartialPivotPrimitiveRoundedU_eq_roundedU_of_rounds`, `noPivotPartialPivotRoundedLUBackwardError`, and `noPivotPartialPivotPrimitiveRoundedLUBackwardError_of_rounds`: for every `ε >= 0`, once the primitive pivoted operations supply `fl(ε/1)=ε`, `fl(ε*1)=ε`, and `fl((-1)-ε)=-1`, the rounded pivoted factors satisfy the componentwise pivoted LU backward-error certificate with radius `ε`. The exact real-arithmetic baseline for §1.12.2 is closed by `repeatedSquare_repeatedSqrt_eq_self` and the displayed 60-step loop by `repeatedSquare_repeatedSqrt_sixty_eq_self`: for any nonnegative `x`, applying 60 square roots and then 60 squarings returns `x`. The displayed HP 48G surrogate function is closed by `hp48gSqrtSquareSurrogate`, including `hp48gSqrtSquareSurrogate_100_eq_one` and `hp48gSqrtSquareSurrogate_relError_100`, which prove the reported `x=100` output and `99/100` relative error for that surrogate; the full source-interval error formulas are closed by `hp48gSqrtSquareSurrogate_absError_of_ge_one`, `hp48gSqrtSquareSurrogate_relError_of_ge_one`, `hp48gSqrtSquareSurrogate_absError_of_nonneg_lt_one`, and `hp48gSqrtSquareSurrogate_relError_of_pos_lt_one`. The exact term-size substrate for §1.12.3 is closed by `inverseSquareTerm_4096_eq_two_pow_neg_24`, `inverseSquareTerm_pos_of_pos`, and `inverseSquareTerm_le_two_pow_neg_24_of_ge`: the `k = 4096` term is exactly `2^{-24}`, and all later inverse-square terms are positive and at most that size. The actual single-precision left-to-right forward summation first-stagnation trace is closed by `inverseSquareSingleEarlyMantissaIncrementRule_closed`, `inverseSquareSingleForwardAccumulator_2896_eq_prePlateauWindowStart`, `inverseSquareSingleForwardAccumulator_2896_add_lt_plateau`, and `inverseSquareSingleForwardAccumulator_4096_add_eq_plateau`: the actual accumulator is below the plateau through `k = 4095`, reaches the displayed plateau at `k = 4096`, and remains there afterward. The local single-precision drop-off mechanism is closed by `inverseSquareSinglePlateau_add_4096_term_rounds_to_self`, `inverseSquareSinglePlateau_add_positive_term_le_two_pow_neg_24_rounds_to_self`, and `inverseSquareSinglePlateau_add_term_rounds_to_self_of_ge_4096`: for the concrete binary32 even-mantissa accumulator printed approximately as `1.64472532`, adding the `4096^{-2}` term is an exact midpoint tie, any smaller positive term no larger than `2^{-24}` is strictly closer to the same accumulator than the next binary32 value, and every later `1/k^2` term rounds back to the same accumulator once the plateau has been reached. The reverse-order loop is now modeled by `inverseSquareSingleReverseAccumulator`, and `inverseSquareSingleReverseAccumulator_ten_pow_nine_split_4096` splits the source's `10^9`-term run into the high-index prefix and the final `4096` low-index terms. Open: the instantiation of the HP 48G root/square phase laws from a concrete calculator model, the reported reverse-order `10^9`-term summation value, and related summation-order examples. |
  HP 48G surrogate law-bridge update:
  `hp48gSqrtSquareTrace_eq_surrogate_of_laws` derives the displayed
  §1.12.2 step surrogate from the compact `Hp48gSqrtSquareSurrogateLaws`
  interface: the 60-square-root phase rounds all inputs `x >= 1` to `1`,
  sends every `0 <= x < 1` to a nonnegative value no larger than
  `hp48gTwelveDigitBelowOne`, and the 60-squaring phase fixes `1` while
  underflowing all nonnegative values at or below that threshold to `0`. This
  is a two-phase symbolic certificate, not a 120-operation or thousands-case
  enumeration. The remaining HP 48G obligation is to instantiate those phase
  laws from a concrete calculator decimal range, rounding, and underflow
  model.
  No-pivot inverse-update update:
  `noPivotIeeeSingle_add_one_normalized_rounds_to_self_of_two_lt_ulp`
  proves the compact binade criterion, and
  `noPivotIeeeSingle_add_one_normalized_rounds_to_self_of_exp_ge_26` with
  `noPivotIeeeSingle_add_one_inv_rounds_to_inv_of_inv_normalized_exp_ge_26`
  closes every positive IEEE-single representable-inverse binade with exponent
  at least `26`, without case enumeration. The ulp-`2` midpoint boundary is
  classified by
  `noPivotIeeeSingle_add_one_normalized_rounds_to_self_of_ulp_eq_two_even`
  and
  `noPivotIeeeSingle_add_one_normalized_rounds_to_succ_of_ulp_eq_two_odd`;
  `noPivotIeeeSingle_add_one_normalized_exp25_even_rounds_to_self` and
  `noPivotIeeeSingle_add_one_inv_rounds_to_inv_of_inv_normalized_exp25_even`
  expose the left-rounding exponent-25 cases, while
  `noPivotIeeeSingle_add_one_normalized_exp25_odd_rounds_to_succ`,
  `noPivotIeeeSingle_add_one_inv_rounds_to_succ_of_inv_normalized_exp25_odd`,
  `noPivotIeeeSingle_add_one_normalized_exp25_max_rounds_to_exp26_min`, and
  `noPivotIeeeSingle_add_one_inv_rounds_to_exp26_min_of_inv_normalized_exp25_max`
  record the corresponding right-rounding boundary cases.
  `noPivotIeeeSingle_add_one_normalized_rounds_to_self_of_left_rounding_cases`
  and
  `noPivotIeeeSingle_add_one_inv_rounds_to_inv_of_inv_normalized_left_rounding_cases`
  package the source-facing left-rounding alternatives into one theorem
  surface. The finite-output guard is closed by
  `noPivotIeeeSingle_add_one_inv_rounds_to_inv_requires_inv_finiteSystem`
  and
  `noPivotIeeeSingle_add_one_inv_not_rounds_to_inv_of_inv_not_finiteSystem`,
  so equality to `epsilon^{-1}` is impossible unless `epsilon^{-1}` is
  finite-format. The earlier
  `noPivotIeeeSingle_add_one_normalized_exp26_rounds_to_self` and
  `noPivotIeeeSingle_add_one_inv_rounds_to_inv_of_inv_normalized_exp26`
  remain as the concrete exponent-26 specialization.
  This records the needed hidden hypothesis explicitly in Lean.
  Pivoted-small-epsilon update: the finite IEEE-single pivoted primitive layer is
  now closed uniformly, not by enumerating cases. The theorems
  `noPivotIeeeSingle_partialPivot_div_epsilon_one_rounds_to_epsilon_of_finiteSystem`
  and
  `noPivotIeeeSingle_partialPivot_mul_epsilon_one_rounds_to_epsilon_of_finiteSystem`
  prove the finite `fl(epsilon/1)=epsilon` and `fl(epsilon*1)=epsilon`
  facts for every finite IEEE-single `epsilon`, while
  `noPivotIeeeSingle_add_one_epsilon_rounds_to_one_of_nonneg_le_small` and
  `noPivotIeeeSingle_partialPivot_sub_neg_one_epsilon_rounds_to_neg_one_of_nonneg_le_small`
  prove the all-small `0 <= epsilon <= 2^-24` pivoted thresholds. The
  §1.12.1 pivoted branch's remaining finite-format gap is therefore no longer
  these supplied primitive facts; the no-pivot source-facing representability
  guard is closed by the finite-output theorems above.
  Update: `inverseSquareTerm_between_half_ulp_and_one_ulp_of_ge_2897_lt_4096` now proves the whole pre-plateau term-size interval, `inverseSquareSingle_add_term_rounds_to_next_of_index_range` composes that interval with the adjacent binary32 successor rule, and `inverseSquareSingleForwardAccumulatorFrom_normalizedValue_of_index_window` lifts the successor step through a recursive accumulator. The window theorem `inverseSquareSingleForwardAccumulatorFrom_prePlateauWindowStart_2897_of_le_1194` proves every intermediate prefix in the 2897--4090 window, `inverseSquareSingleForwardAccumulatorFrom_sixBeforePlateau_4091_of_le_5` proves the intermediate 4091--4095 tail, and `inverseSquareSingleForwardAccumulatorFrom_prePlateauWindowStart_2897_lt_plateau_of_lt_1200` proves the whole 2897--4095 window is still below the plateau. The early prefix is closed without thousands of numeral-by-numeral successor steps: `inverseSquareSingleEarlyMantissaPrefix_2895_eq` certifies the integer mantissa-increment sum for terms `2, ..., 2896`, `inverseSquareSingleEarlyMantissaIncrementNearestCertificate` certifies the strict half-ulp nearest-increment inequalities and mantissa-range bound for each early term, `inverseSquareSingle_add_term_rounds_to_nearest_mantissa_of_scaled_bounds` supplies the finite-format source-rounding bridge, `inverseSquareSingleEarlyMantissaIncrementRule_closed` proves the uniform local early-increment rule, and `inverseSquareSingleForwardAccumulator_2896_eq_prePlateauWindowStart` proves that the actual accumulator reaches the pre-window value. The theorems `inverseSquareSingleForwardAccumulator_2896_add_lt_plateau` and `inverseSquareSingleForwardAccumulator_4096_add_eq_plateau` close the actual below-plateau and plateau conclusions for the left-to-right forward summation.
  Reverse update: `inverseSquareExactReverseAccumulatorFrom`, `inverseSquareTerm_le_telescope`, and `inverseSquareExactReverseAccumulatorFrom_le_telescope` give a symbolic upper-telescoping route for reverse exact prefixes, and `inverseSquareTerm_ge_telescope_succ` with `inverseSquareExactReverseAccumulatorFrom_ge_telescope_succ` gives the matching lower-telescoping route. The concrete theorems `inverseSquareExactReverseTenPowNineHighPrefix_le_inv_4096`, `inverseSquareExactReverseTenPowNineHighPrefix_mem_printedSuffixStartWindow`, and `inverseSquareExactReverseAccumulator_ten_pow_nine_sub_low4096_mem_printedSuffixStartWindow` specialize these bounds to the source's `10^9, 10^9-1, ..., 4097` block, squeezing the exact high-prefix mass into the binary32 start window for the final 4096-term suffix without unfolding the prefix. The refined endpoint `inverseSquareSingleReverseSuffixStartUpperTight` and theorem `inverseSquareExactReverseTenPowNineHighPrefix_mem_printedSuffixStartTightWindow` now record the tighter exact-real window needed for a viable whole-window suffix route. The rounded printed-value proof is reduced either to the high-prefix equality `inverseSquareSingleReverseTenPowNineHighPrefixEqCandidate` plus the closed candidate suffix trace `inverseSquareSingleReverseCandidateSuffixMapsToPrinted_closed`, or to the refined predicates `inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow` and `inverseSquareSingleReverseTightSuffixWindowMapsToPrinted`. The concrete suffix proof uses the `4096` and `4095` anchor steps, the `4094..2049`, `2047..1025`, `1023..513`, `511..257`, `255..129`, `127..65`, `63..33`, `31..17`, `15..9`, and `7..5` same-exponent bands, the `2048`, `1024`, `512`, `256`, `128`, `64`, `32`, `16`, and `8` boundary steps, and the final explicit `4`, `3`, `2`, and `1` additions. The separate high-prefix equality or refined tight-window bridge remains open. The reported rounded reverse value `1.64493406` is therefore reduced to that high-prefix bridge, not to any remaining low-index suffix case split.
  Reverse exact-prefix transfer update: `inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixWindow_of_eq_exact` and `inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow_of_eq_exact` now prove that if the rounded high-index prefix state agrees with the exact high-prefix sum, then it automatically lies in the ordinary and tight final-suffix windows. The endpoint theorems `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_eq_exact` and `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_eq_exact_tight` compose that equality with the corresponding suffix-window certificate to obtain Higham's printed reverse value. The margin definition `inverseSquareSingleReverseHighPrefixTightWindowMargin`, nonnegativity theorem `inverseSquareSingleReverseHighPrefixTightWindowMargin_nonneg`, and bridge `inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow_of_abs_error_le_margin` replace that too-strong equality target by an explicit absolute-error target around the exact high-prefix mass; `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_abs_error_le_margin` composes this error-radius certificate with the tight suffix-window map. The fully explicit rational lower-bound layer `inverseSquareSingleReverseHighPrefixTightWindowMarginLowerBound`, `inverseSquareSingleReverseHighPrefixTightWindowMarginLowerBound_nonneg`, and `inverseSquareSingleReverseHighPrefixTightWindowMarginLowerBound_le_margin` proves a concrete telescoping slack is safely below the exact margin, and the lower-bound transfer theorems `inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow_of_abs_error_le_marginLowerBound` and `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_abs_error_le_marginLowerBound` let future work target that rational bound directly. The sharper shifted-telescope layer `inverseSquareTerm_ge_shifted_telescope_4096_8193`, `inverseSquareExactReverseTenPowNineHighPrefix_ge_shifted_telescope_4096_8193`, `inverseSquareTerm_le_half_telescope`, and `inverseSquareExactReverseTenPowNineHighPrefix_le_half_telescope` gives a much tighter exact high-prefix squeeze; `inverseSquareSingleReverseHighPrefixTightWindowMarginShiftedLowerBound_le_margin` proves the resulting explicit shifted slack is below the true margin, and `inverseSquareSingleReverseTenPowNineHighPrefixCandidate_abs_error_le_shiftedMarginLowerBound` proves the concrete high-prefix candidate is within that stronger slack. The candidate-window layer now also proves `inverseSquareExactReverseTenPowNineHighPrefix_mem_candidateWindow`, the equality-to-candidate-window adapters for the exact prefix and observed candidate, and `inverseSquareSingleReverseHighPrefixCandidateWindow_mem_printedSuffixStartTightWindow`. The narrowed predicate `inverseSquareSingleReverseCandidateWindowMapsToPrinted` and transfer theorem `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_candidateWindow_certificates` reduce the suffix obligation from the whole refined tight window to the 1024-ulp candidate window itself; the old tight-window map still implies the new narrowed map by `inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_tightSuffixWindow`. Subsequent window-band entries now close this narrowed suffix route through `inverseSquareSingleReverseCandidateWindowMapsToPrinted_closed`, and `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_mem_candidateWindow_closed` reduces the reported rounded reverse value to the single remaining membership theorem `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow`, rather than any low-index suffix enumeration.
  High-prefix margin refinement: `inverseSquareSingleReverseHighPrefixCandidateWindowMargin`,
  `inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound`,
  `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowMarginTarget`,
  and
  `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_candidateWindowMarginTarget_closed`
  now reduce the final reverse-order value to one absolute-error inequality
  between the rounded high-prefix state and the exact high-prefix mass. This is
  the compact D1 target; the observed candidate itself satisfies it by
  `inverseSquareSingleReverseTenPowNineHighPrefixCandidate_abs_error_le_candidateWindowMarginShiftedLowerBound`,
  and the `4096` low-index suffix route is already closed.
  Later reverse-suffix frontier update: subsequent 2026-06-13 entries push the
  whole-window suffix obligation past the `2048`, `1024`, `512`, `256`, `128`,
  `64`, `32`, `16`, `8`, and final before-`4` boundary/band chunks. The D2
  suffix frontier is now closed by
  `inverseSquareSingleReverseCandidateWindowMapsToPrinted_closed`; the
  remaining reverse-order frontier is the high-prefix membership theorem
  `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow`.
  High-prefix split update: `inverseSquareTerm_le_two_pow_neg_26_of_ge_8192`,
  `inverseSquareReverseTenPowNineHighPrefix_index_ge_8192`, and
  `inverseSquareTerm_le_two_pow_neg_26_of_reverse_ten_pow_nine_high_binade`
  close the first binade-scale term-size dependency for the earlier
  `10^9, ..., 8193` high-prefix block, while
  `inverseSquareSingleReverseTenPowNineHighPrefixState_split_8192` and
  `inverseSquareExactReverseTenPowNineHighPrefix_split_8192` split the rounded
  and exact high-prefix states into that earlier block followed by
  `8192, ..., 4097`. The same split route now proves
  `inverseSquareExactReverseTenPowNineHighPrefixBefore8192_le_inv_8192` and
  `inverseSquareSingleReverseTenPowNineHighPrefixBefore8192_le_inv_4096`, so
  the earlier exact mass is at most `1/8192` and the earlier rounded state is
  at most `1/4096`. The final-binade budgets
  `inverseSquareExactReverseBinade8192To4097_le_inv_8192` and
  `inverseSquareSingleReverseBinade8192To4097_le_start_add_inv_4096` prove that
  the exact `8192, ..., 4097` mass is at most `1/8192`, and the whole rounded
  binade increases any finite binary32 start by at most `1/4096`. This supports
  a blockwise D1 interval/cell proof route, but
  `inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound_lt_inv_4096`
  proves that the coarse `1/4096` increment budget is still larger than the
  strict finite-cell margin. Thus this split does not close the remaining
  high-prefix membership theorem.
| 826--908 | §1.13 increasing the precision; nonmonotone behavior and examples. | Partly closed. The exact substrate for the `x + a sin(bx)` example is closed by `increasingPrecisionSinExampleSource_perturbation_abs_le`, which defines the source instance `x + 10^{-8} sin(2^{24}x)` and proves its perturbation from `x` has absolute value at most `10^{-8}`. The finite-format plateau certificate route is closed by `finiteRoundToEven_eq_of_strict_closest`, `increasingPrecisionSinExample_finiteRoundToEven_eq_base_of_two_abs_scale_lt_spacing`, and `increasingPrecisionSinExampleSource_finiteRoundToEven_eq_base_of_spacing`: if a finite base point `x` is more than twice the sine amplitude from every other finite-format value, then finite round-to-even of `x+a sin(bx)` returns `x`; for the source amplitude this reduces the plateau obligation to the local spacing condition `2*10^{-8} < |z-x|` for every other finite `z`. The first concrete IEEE-single spacing instance is closed by `increasingPrecisionSinExampleSource_ieeeSingle_roundToEven_one`, which proves that at base point `x = 1` the source expression rounds back to exactly `1` because the perturbation is smaller than the adjacent binary32 gaps around `1`. The exact-storage obstruction behind the source's `x = 1/7` sentence is now closed by `one_seventh_not_binaryTerminating`, `one_seventh_not_ieeeSingleFiniteSystem`, and `one_seventh_not_ieeeDoubleFiniteSystem`: exact `1/7` is not a terminating binary fraction and therefore is not an exact finite value of either IEEE format. The concrete stored source values and representation errors are closed by `increasingPrecision_ieeeSingle_roundToEven_one_seventh`, `increasingPrecision_ieeeDouble_roundToEven_one_seventh`, `increasingPrecision_ieeeSingle_roundToEven_one_seventh_error`, and `increasingPrecision_ieeeDouble_roundToEven_one_seventh_error`: the finite round-to-even selectors return `9586981*2^-26` in IEEE single with error `3/(7*2^26)` and `5146971002709138*2^-55` in IEEE double with error `-2/(7*2^55)`. The early-precision representation-dominance mechanism is now closed by `increasingPrecision_one_seventh_binary_grid_abs_error_ge`, `increasingPrecision_one_seventh_binary_grid_abs_error_gt_scale_of_t_le_twenty_three`, `increasingPrecision_one_seventh_binary_grid_lower_bound_lt_scale_at_twenty_four`, and `increasingPrecisionSinExampleSource_perturbation_lt_one_seventh_binary_grid_error_of_t_le_twenty_three`: every dyadic grid value `z/2^t` is at least `1/(7*2^t)` away from `1/7`, for all `t <= 23` this lower bound is larger than the source sine amplitude `10^-8`, at `t = 24` the universal lower bound has already fallen below that amplitude, and throughout the `t <= 23` range the source sine perturbation is smaller than the input-representation error. The older `t <= 20` theorem remains as a conservative source-language specialization. The contrived branch example at `x = 2/3` is closed at the exact/modelled-rounding level by `increasingPrecisionExampleY_two_thirds_eq_zero`, `increasingPrecisionExampleY_ne_zero_of_ne_two_thirds`, `increasingPrecisionExampleY_pos_of_ne_two_thirds`, `increasingPrecisionExampleExactZ_two_thirds_eq_one`, `increasingPrecisionExampleElseWithExpHat_one_eq_zero`, `increasingPrecisionExampleElse_relError_one_of_expHat_one`, `increasingPrecisionExampleElse_two_precision_failure_of_expHat_one`, and `increasingPrecisionExampleElse_two_precision_failure_of_stored_inputs_expHat_one`: exact arithmetic has `y = 0` and returns `1`; any stored input different from exact `2/3` has positive branch variable and therefore enters the else branch; if the supplied exponential evaluation in that branch is `1`, the modeled result is `0` with relative error `1`; and two such supplied stored-input runs both return `0` with relative error `1` against `f(2/3) = 1`. Open: derive the Fortran 90 single/double precision behavior from an unspecified vendor machine/libm path if that path is required beyond the repository's correctly rounded finite selector model; formalize the Hilbert/Pascal precision plots, instantiate the rest of the binary-rounding plateau over the displayed interval from concrete local spacing certificates, prove the displayed `-8.55e-9` sine perturbation value, and formalize monotonicity/precision-relationship caveats beyond this supplied two-run bridge. |

  Direct dominance update: `increasingPrecisionSinExampleSource_perturbation_lt_one_seventh_binary_grid_error_of_t_le_twenty`
  and
  `increasingPrecisionSinExampleSource_perturbation_lt_one_seventh_binary_grid_error_of_t_le_twenty_three`
  compose the source sine perturbation bound with the dyadic-grid lower bound.
  The conservative theorem proves the source-language `t <= 20` range, while
  the sharper theorem proves every stored input of the form `z/2^t` with
  `t <= 23` has
  `|x+10^-8*sin(2^24*x)-x|` smaller than the input-representation error
  `|x-1/7|`; `increasingPrecision_one_seventh_binary_grid_lower_bound_lt_scale_at_twenty_four`
  records that the universal lower-bound comparison has already flipped at
  `t = 24`.

  Storage update: `two_thirds_not_binaryTerminating` and
  `one_seventh_not_binaryTerminating` prove exact `2/3` and exact `1/7` are not
  terminating binary fractions, `ieeeSingleFormat_finiteSystem_binaryTerminating`
  gives the single-precision analogue of the existing IEEE-double finite-value
  terminating-binary bridge, and
  `two_thirds_not_ieeeSingleFiniteSystem`/`two_thirds_not_ieeeDoubleFiniteSystem`
  plus `one_seventh_not_ieeeSingleFiniteSystem`/
  `one_seventh_not_ieeeDoubleFiniteSystem` prove exact `2/3` and exact `1/7`
  are not finite values of either format.  Consequently
  `increasingPrecisionExampleElse_two_precision_failure_of_ieee_roundToEven_stored_source_expHat_one`
  applies the two-run branch-failure theorem directly to the single and double
  finite round-to-even stored versions of source input `2/3`.  The concrete
  correctly rounded finite-exp trace is now closed by
  `increasingPrecision_ieeeSingle_roundToEven_two_thirds`,
  `increasingPrecision_ieeeDouble_roundToEven_two_thirds`,
  `increasingPrecisionExampleY_ieeeSingle_roundToEven_two_thirds`,
  `increasingPrecisionExampleY_ieeeDouble_roundToEven_two_thirds`,
  `increasingPrecision_ieeeSingle_roundToEven_exp_branch_y_eq_one`,
  `increasingPrecision_ieeeDouble_roundToEven_exp_branch_y_eq_one`, and
  `increasingPrecisionExampleElse_two_precision_failure_of_ieee_roundToEven_stored_exp_source`:
  the stored values are `11184811*2^-24` and `6004799503160661*2^-53`, the
  branch variables are `2^-24/25` and `2^-53/25`, the correctly rounded finite
  exponentials are both `1`, and both modeled runs return `0` with relative
  error `1`.  This closes the repository's concrete round-to-even finite-format
  model for the branch example; a hidden vendor Fortran/libm trace remains open
  unless that implementation is specified by this correctly rounded model.
| 909--1023 | §1.14.1 computing `(e^x - 1)/x`; Algorithm 1, Algorithm 2, log/exp model assumptions, and the roughly `3.5u` relative-error claim. | Partly closed by `CancellationOfRoundingErrors.lean`: `expm1Algorithm1Exact`, `expm1Algorithm2Exact`, `expm1Algorithm1Exact_zero`, `expm1Algorithm2Exact_zero`, and `expm1Algorithm2Exact_eq_algorithm1Exact` formalize the exact branch versions of Algorithms 1 and 2 and prove that exact Algorithm 2 computes the same branch function as exact Algorithm 1, including the removable singularity at `x = 0`. Table 1.2's displayed finite data are closed by `expm1Table12_x_rows`, `expm1Table12_algorithm1_rows`, and `expm1Table12_algorithm2_rows`, with `expm1Table12_algorithm2_ten_pow_neg15_last_digit_correction` formalizing the source note that the `10^-15` Algorithm 2 row should end in `1`; the two page-23 displayed ratio lines are closed as literal decimal-to-rational reductions by `expm1Page23_displayed_single_precision_ratio` and `expm1Page23_displayed_exact_arithmetic_ratio`. The removable singularity of the slow ratio itself is closed by `expm1LogRatio_tendsto_one`, proving `g(y)=(y-1)/log(y)` tends to `1` as `y` tends to `1` through `y != 1`. The page-24 denominator expansion is now closed by `expm1Log_one_add_sub_linear_quadratic_abs_le`, `expm1LogRatioDenRemainder_abs_le`, and `expm1LogRatio_one_add_eq_inv_one_sub_half_add_remainder`: for `|v|<1`, `log(1+v)` has the explicit `v-v^2/2` remainder bound, and for `v != 0`, `g(1+v)` is exactly `(1-v/2+R(v))^{-1}` with `|R(v)| <= |v|^2*(1-|v|)^{-1}/3`. The next printed expansion `g(1+v)=1+v/2+O(v^2)` is closed quantitatively by `expm1LogRatio_one_add_sub_one_add_half_abs_le`, proving `|g(1+v)-(1+v/2)| <= 3|v|^2` for `|v| <= 1/2`, `v != 0`; `expm1LogRatio_sub_one_abs_le` and `expm1LogRatio_self_sub_abs_le` also bound the distance from `g(y)` to `1` and to `y`. The exact two-point linearization substrate for `g(yhat)-g(y) ≈ (yhat-y)/2` is closed by `expm1LogRatio_one_add_diff_sub_half_abs_le`, proving the corresponding `O(w^2+v^2)` error when `yhat=1+w` and `y=1+v` are in the same punctured small neighborhood. The rounded-exponential substitution layer is closed by `expm1LogRatio_mul_one_add_delta_diff_sub_y_delta_half_abs_le`, `expm1LogRatio_mul_one_add_delta_diff_sub_delta_half_abs_le`, and `expm1LogRatio_mul_one_add_delta_diff_sub_logRatio_delta_half_abs_le`, giving explicit bounds around `y*delta/2`, `delta/2`, and `g(y)*delta/2` for `yhat=y*(1+delta)`. The displayed algebra through equation (1.9) is closed by `expm1Algorithm2_yhat_eq_one_implies_x_eq_neg_log_one_add_delta` and `expm1Algorithm2RoundedCore_eq_source_1_9`: if the rounded exponential value `yhat = exp x * (1+delta)` equals `1`, then `x = -log(1+delta)`; otherwise, given a rounded log input `logHat = log(yhat)*(1+epsLog)`, the local rounded subtraction and final division have the source three-epsilon form. The siblings `expm1Algorithm2RoundedCore_eq_source_1_9_of_exact_sub`, `expm1Algorithm2RoundedCore_eq_source_1_9_of_guardDigitSubtractionModel`, and `expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_ferguson` refine this to the guard-digit path: under exact subtraction, under a guard-digit subtraction model plus the Ferguson exponent condition for `yhat,1`, or under concrete finite round-to-even subtraction plus that Ferguson condition, equation (1.9) holds with `epsSub = 0`. The generic gamma bridge `expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma4` combines the three local factors into `g(yhat)*(1+theta)` with `|theta| <= gamma_4`, assuming `gammaValid fp 4` and `0 < 1+epsLog`. Open: concrete exp/log finite-normal/routine instantiation, subtraction operation-link proofs for the actual produced `yhat` on the Sterbenz-radius path (with the Ferguson condition retained only as an alternate adapter), machine-specific MATLAB/IEEE derivation of the Table 1.2 computed columns. The finite-normal rounded-exp/log wrappers now instantiate the source-shaped `3.5u` relative-error theorem, including a source-function target rewrite. |
  Sterbenz-radius update: `expm1Algorithm2_yhat_one_sterbenzRatioCondition_of_abs_sub_one_le_third`
  proves the local `|yhat-1| <= 1/3` radius implies Sterbenz's ratio
  condition for subtracting `1`, and
  `expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_sterbenz_radius`
  uses finite representability of `yhat` and `1` plus the finite round-to-even
  operation link to set `epsSub = 0` in equation (1.9). This replaces the need
  for pointwise Ferguson exponent-case checking on the local small-`x` path.
  The source-shaped wrappers
  `expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_exp_perturb_sterbenz_radius`,
  `expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_exp_x_sterbenz_radius`,
  and
  `expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_exp_x_mul_one_add_u_sterbenz`
  derive the Sterbenz radius directly from `yhat = y*(1+delta)`, from
  `y = exp x` with `|x| <= X`, and from `exp X*(1+u) <= 4/3`, respectively;
  `expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_sterbenz_radius` and
  its source-shaped wrappers expose the exact machine subtraction fact itself,
  while
  `expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_exact_sub`,
  `expm1Algorithm2RoundedCore_relError_le_gamma2_of_exact_sub`,
  `expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_finiteRoundToEven_exp_x_mul_one_add_u_sterbenz`,
  and
  `expm1Algorithm2RoundedCore_relError_le_gamma2_of_finiteRoundToEven_exp_x_mul_one_add_u_sterbenz`
  sharpen the local core factor to `gamma_2` on this exact-subtraction path.
  The finite-output lemmas `FloatingPointFormat.finiteRoundToEven_finiteSystem`,
  `FloatingPointFormat.finiteRoundToEvenOp_finiteSystem`, and
  `FloatingPointFormat.finiteRoundToEvenSqrt_finiteSystem` expose finite
  representability of the source-facing round-to-even selectors, and the
  rounded-exp-produced wrappers
  `expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_rounded_exp_x_mul_one_add_u_sterbenz`,
  `expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_finiteRoundToEven_rounded_exp_x_mul_one_add_u_sterbenz`,
  and
  `expm1Algorithm2RoundedCore_relError_le_gamma2_of_finiteRoundToEven_rounded_exp_x_mul_one_add_u_sterbenz`
  discharge the `yhat` finite-representability hypothesis from
  `yhat = finiteRoundToEven(exp x)`. The finite-normal rounded-exp adapter
  `expm1Algorithm2RoundedExp_delta_abs_le_of_finiteNormalRange` derives
  `|delta| <= fp.u` from the round-to-even normal-range contract for `exp x`
  and `fmt.unitRoundoff <= fp.u`, and the finite-normal wrappers
  `expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_finiteNormal_sterbenz`,
  `expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_finiteRoundToEven_exp_finiteNormal_sterbenz`,
  and
  `expm1Algorithm2RoundedCore_relError_le_gamma2_of_finiteRoundToEven_exp_finiteNormal_sterbenz`
  compose that adapter into the exact-subtraction and `gamma_2` core. The
  rounded-log adapter
  `expm1Algorithm2RoundedLog_exists_contract_of_finiteNormalRange` derives an
  `epsLog` witness, `|epsLog| <= fp.u`, `logHat != 0`, and `0 < 1+epsLog`
  from `logHat = finiteRoundToEven(log yhat)`, finite-normal `log yhat`,
  `fmt.unitRoundoff <= fp.u`, and `fmt.unitRoundoff < 1`; the wrappers
  `expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_finiteRoundToEven_exp_log_finiteNormal_sterbenz`
  and
  `expm1Algorithm2RoundedCore_relError_le_gamma2_of_finiteRoundToEven_exp_log_finiteNormal_sterbenz`
  compose both the rounded-exp and rounded-log finite-normal contracts into
  the local `gamma_2` core. The named predicate
  `finiteRoundToEvenSubtractionLink` captures the routine-level operation link
  `fp.fl_sub = finiteRoundToEvenOp sub`, and the wrappers with suffix
  `_of_subtractionLink` replace the old pointwise produced-`yhat` subtraction
  equality by that single routine-level hypothesis. Remaining concrete
  obligations are exp/log finite-normal/routine instantiation, proving the
  routine-level subtraction link for the selected machine model, and Table 1.2
  machine derivation. The sharper source-shaped `3.5u` bridge now also has
  finite-normal rounded-exp/log wrappers
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_log_finiteNormal`
  and
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_log_finiteNormal_algorithm1Exact`,
  with `expm1LogRatio_exp_eq_algorithm1Exact_of_ne_zero` rewriting the target
  from `g(exp x)` to `(exp x - 1)/x`.
  Denominator update: `expm1LogRatio_abs_ge_one_sub_radius_bound` and
  `expm1LogRatio_abs_ge_half_of_radius` now turn the close-to-one estimate for
  `g(y)` into local lower bounds on `|g(y)|`, including the compact
  `1/2 <= |g(y)|` conclusion for radius `r <= 1/3`.
  Update: the primitive drift bridge `expm1Algorithm2PrimitiveDriftBound`,
  `expm1Algorithm2SlowRatioPerturbationBound_le_of_abs_bounds`,
  `expm1Algorithm2LocalDrift_le_primitive_bound`, and
  `expm1Algorithm2RoundedCore_relError_le_eta_add_gamma4_of_primitive_bounds`
  now reduces future local Algorithm 2 instantiations to elementary absolute-value
  bounds and one normalized budget `primitive <= eta*|g(y)|`; it is deliberately
  not a case-by-case enumeration and still does not instantiate the final
  machine-specific `3.5u` theorem.
  Gamma3 update: `expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma3`,
  `expm1Algorithm2RoundedCore_relError_le_gamma3`,
  `expm1Algorithm2RoundedCore_relError_le_local_bound_gamma3`,
  `expm1Algorithm2RoundedCore_relError_le_eta_add_gamma3`, and
  `expm1Algorithm2RoundedCore_relError_le_eta_add_gamma3_of_primitive_bounds`
  replace the conservative local `gamma_4` arithmetic factor by the source-shaped
  signed-product `gamma_3` factor. With a future drift proof `eta <= u/2`, this
  is the compact route to the first-order `0.5u + 3u` estimate. The corollaries
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_remainder`
  and
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_remainder_of_primitive_bounds`
  now state that route explicitly as `3.5u + ((3u)^2)/(1-3u) +
  (u/2)*gamma_3` under the stronger drift hypothesis. The local-remainder
  theorem
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_local_remainder_of_abs_bounds`
  now derives the same leading `3.5u` term from the ordinary rounded-exponential
  input `|delta| <= deltaAbs <= u`; the remaining gap is to bound its explicit
  slow-ratio remainder from concrete exp/log, guard-digit, and small-`x`
  assumptions. The radius bridge
  `expm1Algorithm2PrimitiveSlowRemainderBound_le_of_radius` and wrapper
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_radius_remainder_of_abs_bounds`
  reduce this remainder to one local-radius expression
  `(6*r^2 + (r/2 + 3*r^2)*u/2)/|g(y)|*(1+gamma_3)`. The denominator-free
  wrapper
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_radius_bound_of_abs_bounds`
  uses `r <= 1/3` to replace this by
  `2*(6*r^2 + (r/2 + 3*r^2)*u/2)*(1+gamma_3)`. The rounded-exponential
  radius bridge `expm1Algorithm2_yhat_sub_one_abs_le_of_y_radius` proves
  `|y*(1+delta)-1| <= r + (1+r)u` from the source hypotheses
  `|y-1| <= r` and `|delta| <= u`, and
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_perturb_radius_bound`
  feeds that combined radius into the denominator-free `3.5u` theorem. The
  source-domain wrapper `expm1Algorithm2_exp_sub_one_abs_le_of_abs_x_le`,
  `expm1LogRatio_exp_ne_zero_of_ne_zero`, and
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_x_radius_bound`
  now packages the printed "small `x` (`y ≈ 1`)" step: `|x| <= X` implies
  `|exp x - 1| <= exp X - 1`, `x != 0` makes `g(exp x)` nonzero, and the
  final local radius is `(exp X - 1) + exp X*u`. The scalar adapter
  `expm1Algorithm2_exp_x_combined_radius_le_third_of_exp_mul_one_add_u_le`
  proves `exp X*(1+u) <= 4/3` is enough for the required `<= 1/3` local
  radius side condition, and
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_x_mul_one_add_u_bound`
  packages that condition directly into the Algorithm 2 theorem. The
  `u`-radius wrapper
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_u_radius_bound_of_abs_bounds`
  further specializes the remaining term to
  `((25/2)*u^2 + 3*u^3)*(1+gamma_3)`. The direct unit-bound wrapper
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_u_radius_bound_of_unit_bounds`
  packages the same result using the actual local assumptions
  `|y-1| <= u`, `|yhat-1| <= u`, and `|delta| <= u`, avoiding any case-by-case
  proof over auxiliary radii when those three inequalities are separately
  proved. The normalized wrapper
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_normalized_remainder_of_abs_bounds`
  reduces that future step to proving
  `expm1Algorithm2PrimitiveSlowRemainderBound yAbs yhatAbs deltaAbs <=
  rem*|g(y)|`.
  Named-bound update: `expm1Algorithm2ThreePointFiveUnitBound` now packages
  the local unit-radius right-hand side. The scalar surface
  `expm1Algorithm2ThreePointFiveUnitBoundScalar` and equality theorem
  `expm1Algorithm2ThreePointFiveUnitBound_eq_scalar` expose the same
  expression with unit roundoff as the variable, and
  `expm1Algorithm2ThreePointFiveUnitBoundScalar_isBigO` proves the local
  envelope is `O(u)` as `u -> 0`. The theorem
  `expm1Algorithm2ThreePointFiveUnitBound_eq_zero_of_u_eq_zero` proves the
  zero-roundoff sanity case, and
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_unit_bound_of_unit_bounds`
  exposes the compact unit-bound theorem. This is still the local Algorithm 2
  bound surface; it does not instantiate concrete exp/log routines or the
  machine-specific Table 1.2 derivation.
| 1024--1084 | §1.14.2 QR factorization; cancellation of rounding errors in Givens QR and backward stability reference to later Theorem 18.9. | The exact displayed embedded Givens block is closed by `givensRotation_trig_orthogonal`, which proves `givensRotation n p q (Real.cos theta) (Real.sin theta)` is orthogonal for distinct coordinates `p != q`. The exact two-component action is closed by `givensRotation_mulVec_p` and `givensRotation_mulVec_q`: `(Gx)_p = c*x_p+s*x_q` and `(Gx)_q = -s*x_p+c*x_q`. The source ratio zeroing algebra is closed by `givensRotation_ratio_zeroes_q` and `givensRotation_ratio_mulVec_p`: choosing `c=a/r` and `s=b/r` sends the affected pair `[a,b]` to second component `0` and first component `(a^2+b^2)/r`. The source zeroing-schedule count is closed by `givensQRRectangularRotationCount` and `givensQRRectangularRotationCount_twice_int`, whose doubled integer identity formalizes `p = n*(m-(n+1)/2)` without natural-number division ambiguity; `givensQRRectangularRotationCount_ten_by_six` proves the Figure 1.5 `10 x 6` case uses `39` rotations. Later QR files also provide Givens QR backward-error surfaces. Open: the specific Chapter 1 worked numerical QR example, its hidden computed intermediate matrices and figure data, and the bridge from that example to the later Theorem 18.9/18.27 backward-error statements. |
| 1085--1133 | §1.15 rounding errors can be beneficial; power method and inverse iteration examples. | Partly closed exactly by `BeneficialRounding.lean`: `beneficialPowerCharDet_eq` proves the displayed matrix has characteristic determinant `lambda*(lambda^2 - (8/5)lambda + 51/100)`, `beneficialPowerCharDet_root_zero`/`beneficialPowerCharDet_root_small`/`beneficialPowerCharDet_root_dominant` prove the exact roots `0` and `4/5 ± sqrt(13)/10`, and `beneficialPowerEigenvalueSmall_display_accuracy`/`beneficialPowerEigenvalueDominant_display_accuracy` prove the two nonzero roots match the source decimals `0.4394` and `1.161` to the displayed precision. The binary storage obstruction is now closed at both the terminating-fraction and finite-format layers: `beneficialPowerMatrix_entry_zero_two_eq_one_fifth` identifies the displayed `(1,3)` entry as `1/5`, `one_fifth_not_binaryTerminating` proves `1/5` is not `z/2^n` by reducing such a representation to the impossible divisibility `5 ∣ 2^n`, and `beneficialPowerMatrix_not_matrixEntriesBinaryTerminating` proves the displayed matrix is not exactly storable entrywise as terminating binary fractions. The bridge `ieeeDoubleFormat_finiteSystem_binaryTerminating` proves every exact IEEE-double finite value is terminating binary by splitting zero/normalized/subnormal cases and using denominator `2^1074`; consequently `one_fifth_not_ieeeDoubleFiniteSystem`, `beneficialPowerMatrix_entry_zero_two_not_ieeeDoubleFiniteSystem`, and `beneficialPowerMatrix_not_matrixEntriesIeeeDoubleFiniteSystem` prove the displayed matrix is not exactly entrywise representable in the repository's IEEE-double finite system. The concrete entrywise rounded-storage first-step vector is now closed: the positive fraction theorems and symmetry wrappers identify the IEEE-double round-to-even values for all displayed matrix fractions used in the first multiplication, `beneficialPowerMatrixIeeeDoubleRounded` defines the entrywise rounded matrix, `beneficialPowerMatrixIeeeDoubleRounded_row_zero_sum_eq`, `beneficialPowerMatrixIeeeDoubleRounded_row_one_sum_eq`, and `beneficialPowerMatrixIeeeDoubleRounded_row_two_sum_eq` prove the three rounded row sums are `2^-54`, `-2^-54`, and `-2^-55`; `beneficialPowerMatrixIeeeDoubleRounded_firstStep_eq` proves the full unnormalized rounded first power-method step is exactly `beneficialPowerMatrixIeeeDoubleRoundedFirstStep`; `beneficialPowerMatrixIeeeDoubleRounded_firstStep_abs_between_one_e17_one_e16` proves every component has magnitude between `10^-17` and `10^-16`, matching the source-scale first-step observation at the entrywise-storage layer; and `beneficialPowerMatrixIeeeDoubleRounded_firstStep_vecNorm2_ge_two_pow_neg54` gives the corresponding concrete norm lower bound. `beneficialPowerMatrix_row_sum_zero` proves every row of the displayed exact matrix sums to zero, `beneficialPowerStart_isRightEigenpair_zero` proves `[1,1,1]^T` is a nonzero right eigenvector for eigenvalue `0`, and `beneficialPowerFirstStep_zero` proves the first exact unnormalized power-method step returns the zero vector. `powerMethodStep_add_matrix` and `beneficialPowerFirstStep_perturbed_eq_delta` close the exact first-step perturbation substrate: if the stored matrix is `A+DeltaA`, the displayed first step is exactly `DeltaA*[1,1,1]^T`; `beneficialPowerFirstStep_perturbed_nonzero_of_delta_row_sum_ne_zero` proves this step is nonzero if some perturbation row sum is nonzero. The inverse-iteration exact substrate is closed at the generic shifted-system/eigenvector layer and now specialized to the displayed zero-eigenvector start: `inverseIterationShiftedMatrix` defines `A-mu I`, `SolvesInverseIterationShiftedSystem` names the solve `(A-mu I)y=x`, `inverseIterationShiftedMatrix_mulVec` proves the action is `A*x-mu*x`, `inverseIteration_shiftedMatrix_mul_eigenvector` proves `(A-mu I)x=(lambda-mu)x` for any right eigenpair `A*x=lambda*x`, `inverseIteration_shiftedSystem_solution_on_eigenvector` proves the exact shifted solve sends an eigenvector right-hand side to `(lambda-mu)^{-1}x` when `lambda-mu != 0`, `inverseIteration_shiftedInverse_mul_eigenvector_of_leftInverse` proves any left inverse of `A-mu I` has the same action on that eigenvector, and `inverseIteration_shiftedInverse_amplification_abs_eq` plus `inverseIteration_shiftedInverse_amplification_strict_of_abs_shift_lt` prove the source's scalar amplification relation that smaller `|lambda-mu|` gives larger exact inverse-iteration amplification. The concrete displayed adapters `beneficialPowerShiftedMatrix_mul_start`, `beneficialPower_inverseIteration_shiftedSystem_solution_start`, and `beneficialPower_shiftedInverse_mul_start_of_leftInverse` prove `(A-mu I)[1,1,1]^T=-mu[1,1,1]^T`, the exact shifted solve returns `(-mu)^{-1}[1,1,1]^T` for `mu != 0`, and any left inverse of the displayed shifted matrix acts that way on the start vector. The exact harmless-direction substrate is now closed conditionally: `matMulVec_smul_right` and `isRightEigenpair_smul` prove nonzero scalar multiples preserve the right-eigenvector direction, and `inverseIteration_parallel_error_output_isRightEigenpair` proves that if the shifted-solve error is supplied as `eta*x`, then the inverse-iteration output `(lambda-mu)^{-1}x + eta*x` remains a right eigenvector for the same eigenvalue when the resulting scalar is nonzero. Open: hidden MATLAB primitive-operation/BLAS matvec and printout trace if that exact implementation path is required, the 38-iteration observation, dominant-eigenpair perturbation theory for the rounded matrix, and the cited inverse-iteration perturbation theorem that supplies the near-parallel solve-error hypothesis. |
| 1085--1133 addendum | §1.15 two-component power-method rate bridge. | Closed non-enumeratively by `powerMethodIterate`, `powerMethodIterate_two_eigencomponents`, `powerMethod_component_abs_ratio_eq_initial_mul_spectral_ratio`, `powerMethod_component_abs_ratio_le_geometric_of_spectral_ratio_le`, and `powerMethod_component_abs_ratio_tendsto_zero_of_spectral_ratio_lt_one`: if a starting vector is a sum of dominant and other right-eigenvector components, `k` unnormalized power-method steps scale those components by the corresponding eigenvalue powers; the non-dominant/dominant scalar ratio is exactly the initial ratio times `(|lambdaOther|/|lambdaDominant|)^k`; any bound by `q` gives a `q^k` geometric estimate; and a spectral ratio strictly below one makes this ratio tend to zero. This closes the two-component linear-rate substrate for the source sentence "the theory says" without proving a full eigenbasis decomposition, identifying the dominant eigencomponent of `A+DeltaA`, deriving the hidden MATLAB/BLAS trace, or proving the 38-iteration observation. |
| 1085--1133 addendum | §1.15 finite-tail power-method convergence bridge. | Closed non-enumeratively by `matMulVec_fin_sum_right`, `vecNorm2_finset_sum_le`, `vecNorm2_fin_sum_le`, `powerMethodIterate_dominant_plus_finite_tail`, `powerMethod_finite_tail_abs_sum_ratio_le_geometric_of_spectral_ratio_le`, `powerMethod_finite_tail_geometric_bound_tendsto_zero`, `powerMethod_finite_tail_abs_sum_ratio_tendsto_zero_of_geometric_bound`, `powerMethod_finite_tail_vecNorm2_ratio_le_geometric_of_spectral_ratio_le`, `powerMethod_finite_tail_vecNorm2_ratio_tendsto_zero_of_geometric_bound`, `powerMethodIterate_dominant_scaled_residual_ratio_le_geometric_of_finite_tail`, `powerMethodIterate_dominant_scaled_residual_tendsto_zero_of_finite_tail`, `PowerMethodDominantFiniteTailCertificate.scaled_residual_tendsto_zero`, and `beneficialPowerStoredStart_dominant_component_certificate_scaled_residual_tendsto_zero`: if a starting vector is a dominant right-eigenvector component plus any finite non-dominant tail of right-eigenvector components, `k` unnormalized power-method steps scale every component by its eigenvalue power; if all finite-tail spectral ratios are bounded by `q`, both the normalized aggregate coefficient magnitude and the normalized Euclidean norm of the finite tail are bounded by initial finite-tail constants times `q^k`; both tail ratios tend to zero when `0 <= q < 1`; and the actual iterate's Euclidean residual after subtracting the dominant component and scaling by the dominant scalar magnitude tends to zero. The certificate handoff now specializes this to the stored §1.15 matrix/start vector once the concrete dominant-eigencomponent certificate is supplied. This closes the finite-family theory and certificate-to-convergence bridge without enumerating components. Remaining open: construct that concrete certificate for the stored `A+DeltaA`, prove its dominant eigenpair/perturbation facts, identify the hidden MATLAB/BLAS trace, and prove the 38-iteration observation. |
| 1085--1133 addendum | §1.15 inverse-iteration near-parallel residual bridge. | The algebraic bridge from a near-parallel shifted-solve error to a small eigen-residual is now closed non-enumeratively by `eigenResidualVec`, `eigenResidualVec_add_parallel_eq`, `eigenResidualVec_norm_le_opNorm_add_abs`, `inverseIteration_near_parallel_error_eigenResidual_eq`, and `inverseIteration_near_parallel_error_eigenResidual_norm_le`. If the solve error decomposes as `eta*x + r`, Lean proves the output residual is exactly `eigenResidualVec A lambda r`; under `opNorm2Le A A_norm`, its norm is at most `(A_norm + |lambda|)*||r||_2`. The displayed §1.15 zero-eigenvector instance is now specialized by `beneficialPower_inverseIteration_near_parallel_error_eigenResidual_eq`, `beneficialPower_inverseIteration_near_parallel_error_eigenResidual_norm_le`, `beneficialPower_inverseIteration_near_parallel_error_eigenResidual_norm_le_of_residual_norm_le`, and `beneficialPower_inverseIteration_near_parallel_error_eigenResidual_norm_le_of_componentwise_common_scalar`, proving the same bridge for `beneficialPowerMatrix` and `beneficialPowerStart` with bounds `A_norm*||r||_2`, `A_norm*eps` from a residual budget, and `A_norm*(sqrt 3*eps)` when every displayed solve-error component is within `eps` of a common scalar `eta`. This replaces any case-by-case proof obligation with one reusable certificate theorem plus displayed-matrix adapters. Still open: prove that a concrete rounded shifted-solve trace satisfies this componentwise/common-direction certificate, or an equivalent near-parallel decomposition, for the source example. |
| 1085--1133 addendum | §1.15 perturbed first power-method step norm bridge. | Closed by `beneficialPowerFirstStep_perturbed_eq_zero_iff_row_sums_zero`, `vecNorm2_pos_of_exists_ne`, `beneficialPowerFirstStep_perturbed_vecNorm2_pos_of_delta_row_sum_ne_zero`, `beneficialPowerFirstStep_perturbed_vecNorm2_eq_zero_iff_row_sums_zero`, `beneficialPowerFirstStep_perturbed_vecNorm2_ge_of_row_sum_abs_ge`, `beneficialPowerFirstStep_perturbed_vecNorm2_le_of_row_sum_abs_le`, and `beneficialPowerFirstStep_perturbed_vecNorm2_le_of_entry_abs_le`: Lean proves the first perturbed power-method vector is zero exactly when every stored-perturbation row sum is zero, its Euclidean norm vanishes exactly under the same condition, any nonzero row sum gives a positive norm, any row-sum magnitude lower bound `rho` is also a lower bound for the norm, every row-sum radius `eps` gives norm at most `sqrt 3*eps`, and every entrywise perturbation radius `eps` gives norm at most `sqrt 3*(3*eps)`. This is the norm-level exact-algebra consequence of the source-visible perturbation substrate, not a concrete IEEE-double perturbation-size or MATLAB iteration trace. |
| 1134--1207 | §1.16 stability depends on the problem; determinant of upper Hessenberg matrices versus solving upper Hessenberg systems. | Partly closed exactly by `ProblemDependentStability.lean`: `hessenbergDiagRoundedStep_eq_perturbed_exactStep` proves the displayed scalar rounded diagonal update is exact upper-Hessenberg diagonal recurrence for perturbed diagonal/subdiagonal entries. `hessenbergEntrywisePerturbation` defines the nearby matrix obtained from `A` by changing diagonal entries to `a_kk*(1+eps3)` and first-subdiagonal entries to `a_k,k-1*(1+eps1)*(1+eps2)*(1+eps3)`, with other entries unchanged; `hessenbergEntrywisePerturbation_diag`, `hessenbergEntrywisePerturbation_subdiag`, and `hessenbergDiagRoundedStep_eq_entrywisePerturbedExactStep` prove the rounded diagonal update is exactly the unrounded recurrence on those nearby matrix entries. The all-updated-diagonals wrapper is now closed by `HessenbergRoundedDiagTraceOnOriginal`, `HessenbergExactDiagTraceOnEntrywisePerturbation`, and `hessenbergRoundedDiagTraceOnOriginal_exactTraceOnEntrywisePerturbation`: if every updated computed diagonal satisfies the source rounded formula on the original entries with stage-indexed epsilons, then every updated computed diagonal also satisfies the exact upper-Hessenberg diagonal recurrence on the single nearby matrix `hessenbergEntrywisePerturbation n A eps1 eps2 eps3`. The quantitative nearby-matrix layer is now closed at the entrywise level: `hessenbergEntrywisePerturbation_isUpperHessenberg` preserves the upper-Hessenberg shape, `hessenbergEntrywisePerturbation_diag_abs_error_le` proves diagonal changes are bounded by `u*|a_kk|`, `hessenbergEntrywisePerturbation_subdiag_signedRelErrorWitness_exists` and `hessenbergEntrywisePerturbation_subdiag_abs_error_le_gamma` package the three subdiagonal factors through `gamma fp 3`, and `hessenbergEntrywisePerturbation_abs_error_le_gamma_three` proves the all-entry bound `|A'ᵢⱼ-Aᵢⱼ| <= gamma fp 3*|Aᵢⱼ|`. `hessenbergDetRoundedProduct_relError_le_gamma` proves the final rounded determinant product has relative error at most `gamma fp n` around the computed diagonal product, `hessenbergDetRoundedProduct_relError_le_gamma_of_det_eq_diag_prod` lifts this to any matrix whose exact determinant equals that diagonal product, and `hessenbergRoundedDiagTraceOnOriginal_nearbyDet_relError_le_gamma` combines the source-shaped rounded trace, the single nearby matrix, and a determinant-product certificate for that nearby matrix to return both the exact nearby trace and the final `gamma_n` relative-error bound against `det(A')`. `hessenbergDetExample_isUpperHessenberg` proves the displayed matrix family is upper Hessenberg, `hessenbergDetExample_mul_ones` computes `A*[1,1,1,1]^T = [alpha-3,0,1,2]^T`, `hessenbergDetExampleMatrixInv_alpha_ten_pow_isInverse` proves the displayed inverse is a two-sided inverse at `alpha=10^-7`, `hessenbergDetExampleMatrix_alpha_ten_pow_infNorm_eq` and `hessenbergDetExampleMatrixInv_alpha_ten_pow_infNorm_eq` prove `||A||∞ = 4` and `||A^{-1}||∞ = 40000000/10000001`, and `hessenbergDetExample_kappaInfProduct_alpha_ten_pow_eq`/`hessenbergDetExample_kappaInfProduct_alpha_ten_pow_near_sixteen` prove the exact condition-number product `160000000/10000001` and its closeness to the source's displayed `16`. `hessenbergDetExampleNoPivotU_blockTriangular` and `hessenbergDetExampleNoPivotU_det_eq_diag_prod` define the exact no-pivot upper triangular endpoint and prove its determinant is the diagonal product; `hessenbergDetExampleNoPivotUDiag_prod_eq`, `hessenbergDetExampleMatrix_det_eq_noPivotUDiag_prod`, and `hessenbergDetExampleMatrix_det_eq` prove the original matrix determinant is preserved by the three row eliminations and equals `2*(alpha+1)` when the denominators are nonzero. `hessenbergDetExampleRoundedProduct_relError_le_gamma` specializes the determinant-product mixed-stability bridge to the displayed matrix family. `hessenbergDetExampleMatrix_alpha_ten_pow_det_eq`, `hessenbergDetExampleMatrix_alpha_ten_pow_det_near_two`, and `hessenbergDetExample_alpha_ten_pow_exact_table_baseline` close the exact source-value Table 1.3 baseline: the determinant is `10000001/5000000`, within `1e-6` of the five-significant-figure value `2`, and the exact solution vector is `e`; `hessenbergDetExample_alpha_ten_pow_roundedProduct_relError_le_gamma` specializes the rounded determinant-product bridge to that exact source value. `hessenbergDetExampleTable13_computedSolution_rows`, `hessenbergDetExampleTable13_exactSolution_rows`, and `hessenbergDetExampleTable13_det_rows` close the printed Table 1.3 data transcription; `hessenbergDetExampleTable13_solution_relative_error_eq` proves the displayed computed solution has relative infinity-norm error `1.3842`; `hessenbergDetExampleTable13_first_component_abs_error_gt_one` and `hessenbergDetExampleTable13_solution_relative_error_gt_one` formalize the printed-data solve-instability contrast; `hessenbergDetExampleTable13_det_relative_error_lt_two_eight` formalizes the displayed determinant accuracy `1.9209e-8 < 2e-8`; and `hessenbergDetExampleTable13_residual_rows`, `hessenbergDetExampleTable13_residual_infNorm_eq`, `hessenbergDetExampleTable13_scaled_residual_eq`, and `hessenbergDetExampleTable13_scaled_residual_gt_one_tenth` prove that inserting the displayed computed solution into the exact source system gives residual rows `[-1.3842e-7,-1.3842,0,0]`, residual infinity norm `1.3842`, and source-scaled residual `6921/47684 > 0.1`. `hessenbergDetExampleFirstMultiplier_alpha_ten_pow` proves the source's large first multiplier is `10^7` for `alpha=10^-7`. The primitive nearest/even Table 1.3 determinant, forward-RHS, and standard back-substitution trace is closed separately in the Table 1.3 row; the standard trace gives `[0,1,1,1]^T`, while the formal adjacent-RHS diagnostic derives the printed first component from the one-step-toward-zero neighbor above `-3`. Open: source attribution for the hidden RHS storage/operation convention behind the printed solution row, or else keeping that solution row as printed table data rather than a derived nearest/even trace from `b=fl32(Ae)`. |
| 1208--1231 | §1.17 rounding errors are not random; Horner/rational-function example. | Closed for the source's theorem-level nonrandomness claim by `NonrandomRounding.lean`: `kahanHornerNumerator` and `kahanHornerDenominator` define the displayed Horner-form rational function, `kahanHornerNumerator_eq_poly` and `kahanHornerDenominator_eq_poly` prove the corresponding quartic expansions, `kahanHornerGridPoint_one`/`kahanHornerGridPoint_succ_sub`/`kahanHornerGridPoint_three_sixty_one` formalize the source grid `x = 1.606 + (k-1)2^-52`, `k=1:361`, `kahanHornerGridPoint_mem_source_interval` and `kahanHornerGridPoint_pairwise_distance_le_source_width` prove the sampled points lie in an interval of width `360*2^-52`, `kahanHornerDenominator_grid_pos_of_one_le_of_le_three_sixty_one` proves the rational denominator is positive at every one of those 361 exact source grid points, and `kahanHornerDenominator_gt_three_on_source_grid_interval` strengthens this to `D > 3` on the full sampled interval. The continued-fraction reference curve is closed at the exact real-arithmetic layer: `kahanContinuedFraction_eq_rationalFunction` derives the continued fraction from the displayed rational function, `kahanContinuedFractionP2_neg_on_source_interval` and `kahanContinuedFractionP1_neg_on_source_interval` discharge the intermediate denominator side conditions on the full source interval, `kahanContinuedFraction_eq_rationalFunction_on_source_interval` proves equality to `r(x)` throughout that interval, `kahanContinuedFraction_grid_eq_rationalFunction` specializes it to all 361 source-grid points, and `kahanContinuedFraction_grid_variation_from_first_lt` proves every continued-fraction reference value on the grid is within `10^-12` of the first. `kahanRationalFunctionFirstDiffKernel_abs_lt_one` and `kahanRationalFunction_first_diff_num_factor` factor and bound the exact reference-function first-difference numerator; `kahanRationalFunction_source_interval_variation_from_first_lt` proves every exact reference value on the whole source interval is within `10^-12` of the first source value; `kahanRationalFunction_grid_variation_from_first_lt` proves the same for every one of the 361 exact source-grid values; `kahanRationalFunction_grid_pair_variation_lt_two` proves any two exact source-grid reference values differ by less than `2*10^-12`; `kahanRoundedGrid_error_spread_gt_of_output_spread` and `ieeeDoubleKahanRationalFunction_grid_error_spread_gt_of_output_spread` prove that any supplied rounded-output spread exceeding this exact-reference spread by `η` forces the rounded-error values themselves to differ by more than `η`; and `kahanRationalFunction_first_to_last_variation_lt` proves the endpoint difference is less than `10^-12`. The rounded-Horner operation trace is closed at the abstract `FPModel` level: `flKahanHornerNumerator_eq_errorEval` gives eight bounded primitive-operation factors for the displayed numerator evaluation, `flKahanHornerDenominator_eq_errorEval` gives seven for the displayed denominator evaluation, and `flKahanRationalFunction_eq_errorEval` adds the final rounded division factor when the computed denominator is nonzero. The concrete IEEE-double operation-order adapter is closed on the whole source interval and grid: `ieeeDoubleKahanNumeratorNormalTrace_of_source_interval`, `ieeeDoubleKahanDenominatorNormalTrace_of_source_interval`, `ieeeDoubleKahanQuotientNormalTrace_of_source_interval`, `ieeeDoubleKahanNumeratorNormalTrace_of_source_grid`, `ieeeDoubleKahanDenominatorNormalTrace_of_source_grid`, and `ieeeDoubleKahanQuotientNormalTrace_of_source_grid` discharge the finite-normal obligations, while `ieeeDoubleKahanRationalFunction_eq_errorEval_on_source_interval` and `ieeeDoubleKahanRationalFunction_grid_eq_errorEval` recover the full numerator/denominator/final-division local-error expansion with strict IEEE-double unit-roundoff factors, without enumerating the 361 points. The selected-pair and stored-grid nonconstancy addenda below close the source statement that the rounded errors are not random; reproducing every plotted marker is optional artifact work, not a separate theorem obligation. |
| 1208--1231 addendum | §1.17 endpoint Figure 1.6 diagnostic. | `kahanRoundedGrid_endpoint_error_spread_gt_of_output_spread` and `ieeeDoubleKahanRationalFunction_endpoint_error_spread_gt_of_output_spread` sharpen the diagnostic bridge for the first and last grid points: since `kahanRationalFunction_first_to_last_variation_lt` proves the exact endpoint reference spread is below `10^-12`, a supplied rounded-output endpoint spread above `10^-12 + η` forces endpoint rounded-error spread above `η`. This lowers the rounded-output certificate needed for an endpoint-only diagnostic and still avoids enumerating all 361 grid values. This endpoint route is superseded for theorem-level §1.17 closure by the stored-input selected-pair diagnostic below; computing endpoint values remains optional plot-reproduction work. |
| 1208--1231 addendum | §1.17 selected-pair Figure 1.6 diagnostic. | Closed for the stored-input IEEE-double Horner route by `NonrandomRounding.lean`. `kahanRationalFunction_grid_175_289_variation_lt_one_e15` proves that the exact reference values at grid points `175` and `289` differ by less than `10^-15`, and `kahanRoundedGrid_175_289_error_spread_gt_of_output_spread` transfers a two-output rounded spread into rounded-error spread. The stored-input definitions `ieeeDoubleKahanStoredGridPoint` and `ieeeDoubleKahanStoredGridRationalFunction` make the IEEE-double input-storage step explicit; `ieeeDoubleKahanStoredGridPoint_175_eq`/`ieeeDoubleKahanStoredGridPoint_289_eq` prove the two source-grid inputs round to `7232781001557191/4503599627370496` and `7232781001557305/4503599627370496`. The selected numerator trace is closed from `fl(4*xstored)` through the final rounded numerator by `ieeeDoubleKahanStoredGridNumerator_m0_175_eq`/`_289_eq`, `ieeeDoubleKahanStoredGridNumerator_s0_175_eq`/`_289_eq`, `ieeeDoubleKahanStoredGridNumerator_m1_175_eq`/`_289_eq`, `ieeeDoubleKahanStoredGridNumerator_s1_175_eq`/`_289_eq`, `ieeeDoubleKahanStoredGridNumerator_m2_175_eq`/`_289_eq`, `ieeeDoubleKahanStoredGridNumerator_s2_175_eq`/`_289_eq`, `ieeeDoubleKahanStoredGridNumerator_m3_175_eq`/`_289_eq`, and `ieeeDoubleKahanStoredGridHornerNumerator_175_eq`/`_289_eq`. The selected denominator trace and final rounded division are closed by `ieeeDoubleKahanStoredGridDenominator_s0_175_eq`/`_289_eq`, `ieeeDoubleKahanStoredGridDenominator_m1_175_eq`/`_289_eq`, `ieeeDoubleKahanStoredGridDenominator_s1_175_eq`/`_289_eq`, `ieeeDoubleKahanStoredGridDenominator_m2_175_eq`/`_289_eq`, `ieeeDoubleKahanStoredGridDenominator_s2_175_eq`/`_289_eq`, `ieeeDoubleKahanStoredGridDenominator_m3_175_eq`/`_289_eq`, `ieeeDoubleKahanStoredGridHornerDenominator_175_eq`/`_289_eq`, and `ieeeDoubleKahanStoredGridRationalFunction_175_eq`/`_289_eq`. The two certified rounded outputs are `4927149988474991/562949953421312` and `2463574994237539/281474976710656`; `ieeeDoubleKahanStoredGridRationalFunction_175_289_error_spread_gt_one_e13` proves their rounded-error spread is greater than `10^-13`. The source-grid existential wrapper `exists_ieeeDoubleKahanStoredGridRationalFunction_grid_error_spread_gt_one_e13` packages this as two valid grid indices whose stored-input rounded errors differ by more than `10^-13`. This closes the selected-pair Figure 1.6 diagnostic without enumerating all 361 grid points. The exact-real-input specialization remains available as a generic bridge, but it is not the observed high-spread route. |
| 1208--1231 addendum | §1.17 selected-pair stored-grid error nonconstancy. | Closed by `ieeeDoubleKahanStoredGridError`, `exists_ieeeDoubleKahanStoredGridError_pair_spread_gt_one_e13`, and `not_forall_ieeeDoubleKahanStoredGridError_eq_on_source_grid`: the certified `k=175`, `k=289` stored-input IEEE-double error spread is repackaged as a named grid-error sequence, and Lean proves that this error sequence is not constant on the 361-point source grid. This is the theorem-level nonrandomness certificate, not a point-by-point plot reproduction. |
| 1208--1231 classification addendum | §1.17 Figure 1.6 theorem obligation. | Source text says Figure 1.6 plots 361 Horner values and that the striking plotted pattern shows the rounding errors are not random. It does not assert exact ordinates for all plotted markers as a theorem. The theorem-level obligation is therefore the rational-function/grid setup, the near-constancy of the exact reference values, the modeled IEEE-double Horner path, and a concrete certificate that the stored-grid rounded errors are not random/nonconstant. These are closed by the selected-pair and stored-grid nonconstancy theorems above. Reproducing every marker of the full plot is classified as optional artifact generation, not a remaining mathematical formalization gap. |
| 1232--1294 | §1.18 designing stable algorithms; six design principles. | Methodological guidance. Could be represented as documentation or a taxonomy, but no mathematical theorem is asserted. |
| 1295--1321 | §1.19 misconceptions; six cautions. | Methodological guidance. No theorem obligation unless the project wants a formal taxonomy. |
| 1322--1506 | §1.20--§1.21 rounding errors in numerical analysis; notes and references. | Proof-source and literature guidance. Not theorem content by itself; relevant citations should be recorded before closing open exercise/example rows. |
| 1507--1614 | Problems 1.1--1.10. | Partly closed. Problem 1.1 is closed by `relErrorComputedDenom`, `relErrorComputedDenom_lower_bound_from_relError`, `relErrorComputedDenom_upper_bound_from_relError`, `relError_lower_bound_from_computedDenom`, `relError_upper_bound_from_computedDenom`, and the packaged `problem_1_1_relError_bounds`, relating the book's `E_rel` and `Etilde_rel` conventions with nonzero-denominator and `< 1` side conditions for the upper envelopes. Problem 1.2 is closed as a table-ambiguity theorem by `problem_1_2_candidateBelow_consistent`, `problem_1_2_candidateInteger_consistent`, and `problem_1_2_table_does_not_force_last_digit_four`: the displayed one-ulp error bars do not force the last digit before the decimal point to be `4`. Problem 1.3 is closed at the exact-identity level by `problem_1_3_sqrt_one_add_sub_one`, `problem_1_3_sin_sub_sin`, `problem_1_3_sq_sub_sq`, `problem_1_3_one_sub_cos_div_sin`, `problem_1_3_lawOfCosines_radicand_sub_rewrite`, `problem_1_3_lawOfCosines_radicand_halfAngle`, and `problem_1_3_lawOfCosines_sqrt_halfAngle`. Problem 1.4 is closed at the exact algebraic formula level by `complexSqrtStable_nonnegA_sq`, `complexSqrtStable_negA_sq`, and `complexSqrtStable_zero_sq`: the stable branches square to `a+i*b` under their explicit branch/nonzero hypotheses. Problem 1.6 is closed as an exact digit-glyph puzzle by `problem_1_6_07734_hello`, `problem_1_6_38079_globe`, `problem_1_6_318808_bobbie`, `problem_1_6_35007_loose`, `problem_1_6_5773857734_hells_bells`, `problem_1_6_3331_ieee`, `problem_1_6_5607_logs`, and `problem_1_6_real_sqrt_31438449_eq_5607`. Problem 1.7 is closed at the first-order finite-difference derivation, displayed closed-form algebra layer, and literal relative-remainder `O(t^2)` layer by `sampleVarianceTwoPass_add_scaled_sub_eq`, `sampleVarianceDirectionalCoeff_componentwise_le`, `sampleVarianceDirectionalCoeff_normwise_le`, `sampleVarianceKappaNClosed_eq_expanded`, `sampleVarianceKappaCClosed_le_KappaNClosed`, `sampleVarianceTwoPass_relative_add_scaled_sub_linear_eq_remainder`, and `sampleVarianceProblem17RelativeRemainderEnvelope_isBigO`. Problem 1.8 is closed at the exact recurrence/qualitative-instability layer by `mullerExact_initial0`, `mullerExact_initial1`, `mullerExact_satisfies_recurrence`, `mullerExact_lt_succ`, `mullerExact_tendsto_six`, `problem_1_8_x34_rounds_to_5_998`, `mullerModeY_linear_recurrence`, `mullerModeRatio_eq_hundred_sub`, and `mullerModeRatio_gt_99_of_dominant`; the concrete four-significant-decimal displayed recurrence trace is closed by `mullerDecimal4Trace_rounding_intervals`, `mullerDecimal4Trace_34_eq_100`, and `mullerDecimal4Trace_34_abs_error_gt_94`. A full IEEE primitive-operation trace for a named machine remains open. Problem 1.5's exact/log-error core and supplied rounded-outer-exp composition are closed by `expOneApproxLogExpExact_eq_exact_base`, `expOneApproxLogExpWithLogRelError_eq_exact_base_mul_exp`, `expOneApproxLogExp_logRelError_exponent_abs_le`, `expOneApproxLogExpRoundedOuter_eq_exact_base_mul_exp_mul`, and `expOneApproxLogExpRoundedOuter_relError_le_fp`, while Table 1.1 displayed finite data is closed by `expOneApproxTable11_n_rows`, `expOneApproxTable11_computed_rows`, and `expOneApproxTable11_relativeError_rows`; concrete exp/log routine instantiation and a concrete Fortran execution derivation remain open. Problem 1.9's denominator-exact rounded-numerator-to-forward/residual-error bridge is closed through the displayed condition-number forms by `cramer2x2Solution_relative_forward_error_from_flNumerators_exact_den_condAt` and `cramer2x2Residual_infNorm_from_flNumerators_exact_den_condInv`. Problem 1.10 is now closed through the modeled two-pass path, including the source linear term `(n+3)u` plus an explicit higher-order remainder. |

Problem 1.8 hidden-mode addendum: the qualitative contamination layer now has
the quantified dominance theorem
`mullerModeRatio_gt_99_of_one_le_of_two_le` and the concrete source-index
closure `mullerModeRatio_one_34_within_one_of_hundred`.  Lean proves that every
unit-or-larger `100^k` contaminant dominates from `k >= 2`, and specializes this
at `k = 34` to put the hidden-mode ratio in `(99,100)`, hence within one unit of
the spurious root `100`.  This is a compact source-index witness for the hidden
mode, not a full IEEE primitive-operation trace for a named machine path.

Problem 1.5 finite round-to-even addendum: the broad "concrete exp/log routine
instantiation" wording in the Problems 1.1--1.10 row is now closed for the
finite round-to-even selector by
`expOneApproxLogExpFiniteRoundToEven_exists_contract_of_finiteNormalRange` and
`expOneApproxLogExpFiniteRoundToEven_relError_le_fp_of_finiteNormalRange`.
The same Problem 1.5 layer now has the literal first-order theorem
`expOneApproxLogExpUnitRoundoffEnvelope_isBigO`, proving the scalar envelope
`exp(u)*(1+u)-1` is `O(u)` as `u -> 0`. The remaining routine-level gap is a
full named libm/IEEE or Fortran execution derivation beyond this finite-normal
round-to-even wrapper.

Section 1.9 update synchronization note: the rounded prefix-mean trajectory is
closed by `flPrefixMeanTrajectory_abs_error_le_budget`, and the rounded
corrected-sum-of-squares trajectory driven by those rounded means is closed by
`flPrefixCorrectedSumSquaresTrajectory_abs_error_le_budget`. The final rounded
variance quotient is closed by `flSampleVarianceUpdate_abs_error_le_budget`.

Section 1.16 synchronization note: the generic 4-by-4 upper-Hessenberg
no-pivot endpoint and staged determinant-preservation layer is now closed by
`hessenberg4NoPivotEndpoint_blockTriangular`,
`hessenberg4NoPivotEndpoint_det_eq_diag_prod`,
`hessenberg4NoPivotDiag_exactTraceOnMatrix`, and
`hessenberg4NoPivotDiag_exactTraceOnEntrywisePerturbation`, together with
`hessenberg4NoPivotStage1_det_eq`, `hessenberg4NoPivotStage2_det_eq`,
`hessenberg4NoPivotStage3_det_eq`,
`hessenberg4NoPivotStage3_eq_endpoint`,
`hessenberg4NoPivot_det_eq_diag_prod_of_upperHessenberg`,
`hessenberg4NoPivotEntrywisePerturbation_det_eq_diag_prod_of_upperHessenberg`,
and `hessenberg4NoPivotRoundedTrace_nearbyDet_relError_le_gamma`. This proves
the symbolic upper-triangular endpoint determinant is the product of its
symbolic diagonal entries, that the symbolic endpoint diagonal follows the exact
upper-Hessenberg recurrence for the generic matrix and the nearby
entrywise-perturbation matrix, and that the nearby matrix determinant is
preserved through the three symbolic no-pivot row eliminations under the
explicit nonzero-pivot hypotheses, without enumerating cases beyond the fixed
4-by-4 shape. The remaining §1.16 implementation-facing gap is the separate
primitive single-precision Table 1.3 trace.

Section 1.16 Table 1.3 input-storage synchronization note:
`hessenbergDetExampleTable13SourceAlpha`,
`hessenbergDetExampleTable13StoredAlpha`,
`hessenbergDetExampleTable13StoredMatrix`, and
`hessenbergDetExampleTable13StoredRhs` now name the concrete binary32 storage
frontier. Lean proves via
`hessenbergDetExampleTable13StoredAlpha_eq_normalizedValue` and
`hessenbergDetExampleTable13StoredAlpha_eq` that `fl32(10^-7)` is the concrete
normalized value with mantissa `14073749` and exponent `-23`, equivalently
`14073749/2^47`; `hessenbergDetExampleTable13StoredAlpha_pos` and
`hessenbergDetExampleTable13StoredAlpha_ne_zero` close the first stored-pivot
nonzero fact. Lean also proves via
`hessenbergDetExampleTable13_storedMatrix_eq_storedAlpha_matrix` that storing the
source matrix changes only the nonrepresentable `alpha = 10^-7` entry, replacing
it by `fl32(alpha)`, while `0`, `1`, and `-1` are stored exactly;
`hessenbergDetExampleTable13StoredMatrix_isUpperHessenberg`,
`hessenbergDetExampleTable13StoredMatrix_det_eq`, and
`hessenbergDetExampleTable13StoredMatrix_det_eq_noPivotUDiag_prod` then close the
upper-Hessenberg shape and exact no-pivot determinant product for this stored
matrix. The first primitive no-pivot division is now closed by
`hessenbergDetExampleTable13_round_one_div_storedAlpha` and
`hessenbergDetExampleTable13StoredMatrix_firstMultiplier_rounds_to_ten_pow_seven`:
nearest/even binary32 rounds `1/fl32(alpha)` to exactly `10^7`. The first row
update is now partly closed by
`hessenbergDetExampleTable13_round_ten_pow_seven_mul_neg_one`,
`hessenbergDetExampleTable13_round_one_sub_neg_ten_pow_seven`,
`hessenbergDetExampleTable13_round_neg_one_sub_neg_ten_pow_seven`, and the nested
matrix-entry wrappers
`hessenbergDetExampleTable13StoredMatrix_firstStage_diag11_rounds_to`,
`hessenbergDetExampleTable13StoredMatrix_firstStage_super12_rounds_to`, and
`hessenbergDetExampleTable13StoredMatrix_firstStage_super13_rounds_to`: the
product `fl32(10^7*(-1))` is `-10^7`, the updated `(1,1)` entry is `10000001`,
and the updated `(1,2)` and `(1,3)` entries are both `9999999`. The second
primitive multiplier division is now closed by
`hessenbergDetExampleTable13_round_one_div_firstStageDiag_eq_normalizedValue`,
`hessenbergDetExampleTable13_round_one_div_firstStageDiag`, and
`hessenbergDetExampleTable13StoredMatrix_secondMultiplier_rounds_to`:
nearest/even binary32 rounds `1/10000001` to the concrete value
`14073747/2^47`. The second-stage product and two affected upper-triangular
updates are now partly closed by
`hessenbergDetExampleTable13_round_secondMultiplier_mul_firstStageSuper`,
`hessenbergDetExampleTable13_round_one_sub_secondStageProduct`,
`hessenbergDetExampleTable13_round_neg_one_sub_secondStageProduct`,
`hessenbergDetExampleTable13StoredMatrix_secondStage_diag22_rounds_to`, and
`hessenbergDetExampleTable13StoredMatrix_secondStage_super23_rounds_to`:
`fl32((14073747/2^47)*9999999)=4194303/4194304`, the updated `(2,2)` entry is
`1/4194304`, and the updated `(2,3)` entry is `-8388607/4194304`. The final
elimination step is now closed by
`hessenbergDetExampleTable13_round_one_div_secondStageDiag`,
`hessenbergDetExampleTable13_round_thirdMultiplier_mul_secondStageSuper`,
`hessenbergDetExampleTable13_round_one_sub_thirdStageProduct`,
`hessenbergDetExampleTable13StoredMatrix_thirdMultiplier_rounds_to`, and
`hessenbergDetExampleTable13StoredMatrix_finalDiag_rounds_to`:
`fl32(1/(1/4194304))=4194304`,
`fl32(4194304*(-8388607/4194304))=-8388607`, and the final `(3,3)` diagonal entry
is `8388608`. The left-to-right determinant product is now closed by
`hessenbergDetExampleTable13_round_storedAlpha_mul_firstStageDiag`,
`hessenbergDetExampleTable13_round_detProduct01_mul_secondStageDiag`,
`hessenbergDetExampleTable13_round_detProduct012_mul_finalDiag`,
`hessenbergDetExampleTable13_detProduct_leftToRight_rounds_to`, and
`hessenbergDetExampleTable13_detProduct_relError_eq`: the product of the closed
computed diagonals rounds to `8388609/4194304`, and its exact relative error
against the source determinant is `12589/655360065536`.
`hessenbergDetExampleTable13_detProduct_computedDisplay_near` proves this computed
determinant prints as `2.0000`, and
`hessenbergDetExampleTable13_detProduct_relError_matches_display` proves the exact
relative error agrees with the table's `1.9209e-8` to the displayed precision. The
RHS trace is now started by `hessenbergDetExampleTable13_storedRhs_rows`,
`hessenbergDetExampleTable13_round_sourceAlpha_sub_three`,
`hessenbergDetExampleTable13StoredRhs0_eq_neg_three`,
`hessenbergDetExampleTable13StoredRhs_firstStage_rhs1_rounds_to`,
`hessenbergDetExampleTable13StoredRhs_secondStage_rhs2_rounds_to`, and
`hessenbergDetExampleTable13StoredRhs_finalStage_rhs3_rounds_to`: Lean exposes the
stored RHS as `[fl32(alpha-3),0,1,2]^T`, proves `fl32(alpha-3)=-3`, and proves the
first RHS elimination update
`fl32(0 - fl32(10^7*(-3))) = 30000000`, the second RHS update
`-4194303/2097152`, and the final RHS update `8388608`. The standard
nearest/even binary32 back-substitution trace is now closed by
`hessenbergDetExampleTable13_standardBackSubSolution_rows`, which gives
`[0,1,1,1]^T`, and
`hessenbergDetExampleTable13_standardBackSub_first_component_ne_printed` proves
that its first component is not the printed Table 1.3 value `2.3842`. The
adjacent-RHS diagnostic is now formalized by
`hessenbergDetExampleTable13AltStoredRhs0`,
`hessenbergDetExampleTable13_neg_three_altStoredRhs0_adjacent`,
`hessenbergDetExampleTable13StoredRhs0_lt_altStoredRhs0`,
`hessenbergDetExampleTable13_altRhsBackSub_x0_rounds_to_printed_float`, and
`hessenbergDetExampleTable13_altRhsBackSub_first_component_matches_printed`:
the alternate value is the immediate binary32 neighbor above `-3`, the actual
nearest/even stored first RHS entry is strictly below it, and if only that
entry is replaced by the adjacent value `-12582911/4194304`, then the same
standard back-substitution path returns `78125/32768`, which is within half a
unit in the fifth displayed decimal place of the table's `2.3842`. Thus the
remaining Table 1.3 gap is no longer a large trace search: it is the source
attribution question of whether the printed solution row used that hidden RHS
storage/operation convention, or whether the row must remain a printed datum
rather than a derived nearest/even trace from `b = fl32(Ae)`.

Ledger synchronization note: the Problem 1.10 support layer now also includes
`exists_weightedRelativeErrorFactor_of_nonneg_sum`, which collapses
componentwise squared-deviation perturbations with nonnegative weights into a
single aggregate relative factor, plus
`flSampleVarianceTwoPassWithMean_eq_mul_one_add_gamma`, which proves the
fixed-supplied-mean rounded second pass has one relative factor bounded by
`gamma fp (n+3)`. This closes the modeled subtraction/squaring/summation/division
part of Problem 1.10 for a fixed `m`; `flSampleMean_backward_error` now also
closes the first-pass mean as a componentwise backward-error statement, and
`flSampleMean_abs_error_le_gamma` gives the corresponding absolute mean-error
bound. `flSampleVarianceTwoPass_relError_le_gamma_add_mean_quadratic` composes
these with the rounded second-pass theorem into a true-variance relative-error
bound with the exact mean-error quadratic left explicit, and
`flSampleVarianceTwoPass_mean_quadratic_le_gamma_sq` plus
`flSampleVarianceTwoPass_relError_le_gamma_add_gamma_sq_mean_bound` bound that
quadratic by the square of the first-pass `gamma fp n` mean-error radius. The
helper `gamma_eq_linear_plus_quadratic_remainder` and the theorem
`flSampleVarianceTwoPass_relError_le_linear_u_add_explicit_remainder` rewrite
the bound into the source linear term `(n+3)u` plus an explicit higher-order
remainder. The separate Landau theorem
`flSampleVarianceTwoPassProblem110RemainderQuadraticEnvelope_isBigO` now closes
the literal `O(u^2)` notation layer for the explicit quadratic envelope.

Problem 1.10 named-remainder update: `flSampleVarianceTwoPassProblem110MeanQuadraticBound`
now names the bounded first-pass mean contribution,
`flSampleVarianceTwoPassProblem110Remainder` names the full explicit
higher-order remainder after the source linear term `(n+3)u`, and
`flSampleVarianceTwoPassProblem110MeanQuadraticBound_nonneg` plus
`flSampleVarianceTwoPassProblem110Remainder_nonneg` prove the named terms are
nonnegative under the ordinary positive-variance and `gammaValid fp (n+3)`
guards. The theorem
`flSampleVarianceTwoPass_relError_le_linear_u_add_problem110_remainder`
restates the source-style bound in the auditable form
`relError <= (n+3)u + flSampleVarianceTwoPassProblem110Remainder fp x`.
The non-vacuity checks
`flSampleVarianceTwoPassProblem110MeanQuadraticBound_eq_zero_of_u_eq_zero`,
`flSampleVarianceTwoPassProblem110Remainder_eq_zero_of_u_eq_zero`, and
`flSampleVarianceTwoPass_relError_eq_zero_of_u_eq_zero` prove that when
`fp.u = 0`, the named higher-order remainder and the modeled relative error
both vanish.
The definition `flSampleVarianceTwoPassProblem110RemainderQuadraticBound` and
the theorem `flSampleVarianceTwoPassProblem110Remainder_le_quadratic_bound`
add the source-style `O(u^2)` certificate: under `(n+3)u <= 1/2`, the named
remainder is bounded by an explicit quadratic expression in `u`, with the
data-dependent coefficient displayed in the definition.

## Not-Proved Ledger

| ID | Source | Open obligation | Current blocker / next Lean step |
|---|---|---|---|
| C1F.1 | §1.6 | General multivariate/normed conditioning definitions and the general condition-number forward-error principle. | Finite-vector normwise backward-error, condition-bound, supremum/attained-maximum surfaces, and forward-error principles are closed by `normwiseBackwardErrorBoundedVec`, `normwiseConditionNumberBoundedVec`, `normwiseConditionNumberSupremumVec`, `normwiseConditionNumberAttainedVec`, `normwiseConditionNumberSupremumVec_of_attained_bound`, `normwise_forward_from_backward_vec`, and `normwise_forward_from_backward_vec_of_condition_supremum`. No paper-level §1.6 blocker remains; concrete compactness/attainment theorems are future specializations for selected norm/domain packages. |
| C1F.2 | §1.7 | Floating-point comparison for the trigonometric cancellation example. | Exact identity `1 - cos x = 2 sin^2(x/2)` is closed by `one_sub_cos_eq_two_sin_sq_half`; the source scaled-target range and supplied-approximation comparison layer are closed by `trigCancellationExactScaled_le_half`, `trigCancellationExactScaled_lt_half`, `trigCancellationDirectScaledFromCos_abs_error_le`, and `trigCancellationRewriteScaledFromSinHalf_abs_error_le_direct_cos_bound`; the finite round-to-even trig-output wrapper is closed by `trigCancellationDirectScaledFiniteRoundToEvenCos_abs_error_le`, `trigCancellationRewriteScaledFiniteRoundToEvenSinHalf_abs_error_le`, and `trigCancellationRewriteScaledFiniteRoundToEvenSinHalf_abs_error_le_direct_cos_bound`; and the displayed ten-significant-figure arithmetic example is closed by `trigCancellationDirectScaled_eq`, `trigCancellationDirectScaled_ne_half`, and `trigCancellationRewriteScaled_eq_half`. Remaining gap: instantiate full named libm/IEEE-library sine/cosine routines beyond this finite round-to-even output selector, if those routines are required. |
| C1F.3 | §1.8 | Floating-point stable quadratic-root computation. | Exact quadratic polynomial/root API, product-recovery algebra, the two displayed `10^20` exact root examples, and the exact variable-scaling identity are closed by `Quadratic.lean`. The source-level sign-of-`b` larger-root selector and direct numerator-cancellation comparisons are closed by `quadraticRootSmallByBSign_abs_le_largeByBSign`, `quadraticRootPlus_abs_le_rootMinus_of_b_nonneg`, `quadraticRootMinus_abs_le_rootPlus_of_b_nonpos`, `quadraticRootPlusNumerator_abs_le_of_b_nonneg_s_close`, and `quadraticRootMinusNumerator_abs_le_of_b_nonpos_s_close`. The rounded discriminant operation trace, named absolute-error radius, and conditional nonnegativity certificate are closed by `flQuadraticDiscriminant_expansion`, `flQuadraticDiscriminant_abs_error_le`, and `flQuadraticDiscriminant_nonneg_of_abs_error_bound_le`; the abstract higher-precision discriminant path is closed by `flQuadraticDiscriminantAbsErrorBound_eq_poly`, `flQuadraticDiscriminantAbsErrorBound_le_of_u_le`, `flQuadraticDiscriminantAbsErrorBound_le_of_simulatesHigherPrecision`, `flQuadraticRootPlusMixedDiscriminantSqrt_abs_error_le`, and `flQuadraticRootMinusMixedDiscriminantSqrt_abs_error_le`. The small-discriminant guard-failure case is closed at the exact real-root cluster layer by `quadraticRootPlus_sub_midpoint_abs_eq`, `quadraticRootMinus_sub_midpoint_abs_eq`, `quadraticRootSeparation_abs_eq`, `quadraticRoots_near_midpoint_of_discriminant_le`, and `quadraticRoots_near_midpoint_of_discriminant_guard_failure`. The rounded standard-formula branch micro-kernel with a supplied square-root value is closed by `flQuadraticRootPlusFromSqrt_rel_error_le_gamma3` and `flQuadraticRootMinusFromSqrt_rel_error_le_gamma3`. The supplied relative-error, absolute-error, and discriminant-error input bridges are closed by `flQuadraticRootPlusWithSqrtRelError_abs_error_le`, `flQuadraticRootMinusWithSqrtRelError_abs_error_le`, `flQuadraticRootPlusFromSqrt_abs_input_error_le`, `flQuadraticRootMinusFromSqrt_abs_input_error_le`, `flQuadraticRootPlusFromSqrt_discriminant_abs_error_le`, and `flQuadraticRootMinusFromSqrt_discriminant_abs_error_le`. The rounded-discriminant/square-root path is closed conditionally by `flQuadraticRootPlusRoundedDiscriminantSqrt_abs_error_le` and `flQuadraticRootMinusRoundedDiscriminantSqrt_abs_error_le` under the separation guard `flQuadraticDiscriminantAbsErrorBound fp a b c <= quadraticDiscriminant a b c`; the mixed-precision branch path uses the corresponding discriminant-precision guard with root-precision square-root/branch arithmetic. The abstract computed-square-root path for an exact real discriminant is closed by `flQuadraticRootPlusComputedSqrt_abs_error_le` and `flQuadraticRootMinusComputedSqrt_abs_error_le`, using `FPModel.model_sqrt`. The rounded recovery operation itself is closed by `flQuadraticRecoveredRootFromOther_rel_error_le_gamma2`, and the supplied/computed branch-to-recovered-root accuracy layer is closed by `flQuadraticRecoveredRootFromOther_abs_error_le_of_abs_error`, `flQuadraticRecoveredRootMinusFromPlus_abs_error_le`, `flQuadraticRecoveredRootPlusFromMinus_abs_error_le`, `flQuadraticRecoveredRootMinusFromRoundedPlusDiscriminantSqrt_abs_error_le`, and `flQuadraticRecoveredRootPlusFromRoundedMinusDiscriminantSqrt_abs_error_le` under the explicit branch-error-smaller-than-root guard. The total sign-of-`b` rounded pair is closed conditionally by `flQuadraticRootsByBSignRoundedDiscriminantSqrt_abs_error_le`, under the discriminant separation guard and the branch-radius-smaller-than-root guard. The displayed single-precision overflow-range fact, displayed double normal-range discriminant-path facts, scaled single normal-range intermediates, and actual rounded-intermediate IEEE double/twice discriminant trace are closed by the `quadraticOverflowExample_*` and `quadraticOverflowExample_*doubleRounded*` theorem families, including normal-range, nearest/even standard-model, no-flag, value-field, and source-facing wrapper `quadraticOverflowExample_singleOverflow_doubleRoundedDiscriminantTrace`. Remaining IEEE scope is full special-value/trap semantics beyond this displayed finite-range example, not the displayed double/twice operation trace itself. |
| C1F.3 addendum | §1.8 displayed twice-precision operation trace | `quadraticOverflowExample_singleOverflow_doubleRoundedDiscriminantTrace` now packages the displayed finite trace: the single-precision `b*b` primitive overflows, but the corresponding IEEE-double rounded-intermediate discriminant path has normal-range exact primitive results, no flags, and operation-result value fields equal to `quadraticOverflowExample_b_square_doubleRounded`, `quadraticOverflowExample_four_a_doubleRounded`, `quadraticOverflowExample_four_ac_doubleRounded`, and `quadraticOverflowExample_discriminant_doubleRounded`. The remaining §1.8 implementation scope is full IEEE special values, traps, and flag semantics beyond this finite displayed path, not the displayed double/twice trace itself. |
| C1F.4 | §1.9 | Sample variance floating-point stability claims. | Closed by `SampleVariance.lean` at the exact formula, exact Welford-prefix recurrence, exact `[10000,10001,10002]` update example, aggregate cancellation/negative-output criterion, concrete binary32 one-pass zero/relative-error-one trace, Problem 1.7 condition-number algebra, and Problem 1.10 two-pass rounded-transfer layers. New closure: `flPrefixMeanTrajectory_abs_error_le_budget` composes the rounded mean-update step through all prefixes with a recursive absolute-error budget, `flPrefixCorrectedSumSquaresTrajectory_abs_error_le_budget` composes the corrected-sum-of-squares update through all prefixes while charging the propagated rounded-mean error, and `flSampleVarianceUpdate_abs_error_le_budget` closes the final rounded variance quotient for `n > 1`. The nonnegative budget theorems are `flPrefixMeanTrajectoryAbsErrorBudget_nonneg`, `flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget_nonneg`, and `flSampleVarianceUpdateAbsErrorBudget_nonneg`. No theorem-level blocker remains for the source negative-output claim; upstream FP accumulation to a concrete negative aggregate remains optional implementation provenance. The Problem 1.7 relative-remainder envelope and the Problem 1.10 coefficient-times-`u^2` envelope now have literal Landau theorems. |
| C1F.4 addendum | §1.9 supplied negative final-operation trace | `sampleVarianceOnePassIeeeSingleNegativeAggregateTrace_eq_neg_sixteen`, `sampleVarianceOnePassIeeeSingleNegativeAggregateTrace_lt_zero`, and `sampleVarianceOnePassIeeeSingleNegativeAggregateTrace_relError` close a finite binary32 final-operation diagnostic from supplied rounded aggregates: `300059968 - 300060000` rounds exactly to `-32`, division by `2` rounds exactly to `-16`, and the result has relative error `17` against the exact `[10000,10001,10002]` variance. This narrows the former negative-output trace gap without claiming a different actual accumulation path; the existing concrete binary32 source trace still returns `0`, and upstream accumulation into the supplied negative aggregate pair remains the only optional implementation-path gap. |
C1F.4 Problem 1.10 update: `flSampleVarianceTwoPassProblem110RemainderQuadraticBound`,
`flSampleVarianceTwoPassProblem110RemainderQuadraticCoeff`,
`flSampleVarianceTwoPassProblem110RemainderQuadraticBound_eq_coeff_mul_u_sq`,
`flSampleVarianceTwoPassProblem110RemainderQuadraticEnvelope`,
`flSampleVarianceTwoPassProblem110RemainderQuadraticEnvelope_eq_bound`,
`flSampleVarianceTwoPassProblem110RemainderQuadraticEnvelope_isBigO`, and
`flSampleVarianceTwoPassProblem110Remainder_le_quadratic_bound` now give the
explicit quadratic-in-`u` envelope for the named higher-order remainder under
`(n+3)u <= 1/2`, identify the FP-model envelope as a fixed data-dependent
coefficient times `u^2`, and prove the scalar envelope is literally `O(u^2)` as
`u -> 0`.
| C1F.6 | §1.10.1 | GEPP versus Cramer's rule 2-by-2 stability comparison. | Exact 2-by-2 Cramer determinant/formula correctness is closed by `CramersRule.lean`; the Problem 1.9 denominator-exact rounded-numerator bridge and both displayed condition-number forms are closed by `cramer2x2Solution_error_from_flNumerators_exact_den`, `cramer2x2Solution_relative_forward_error_from_flNumerators_exact_den_condAt`, and `cramer2x2Residual_infNorm_from_flNumerators_exact_den_condInv`; the rounded-exact-solution residual/scaled-residual comparison is closed by `roundedExactSolution_residual_norm_le_opNorm2_mul_relative_error`, `relativeResidual2`, and `roundedExactSolution_relativeResidual2_le_relative_error_factor`; and the later-LU GEPP `n = 2` scaled-residual bridge is closed by `gepp2_relativeResidual2_le_wilkinson`. The displayed MATLAB solution/scaled-residual rows are now closed as exact rational data by the `...ScaledResidual...` theorem names; `cramerGeppExample_scaledResidual_component_gap` proves each printed Cramer scaled-residual component is more than `10^9` times the corresponding printed GEPP scaled-residual component in absolute value; `cramerGeppExample_scaledResidual_infNorm_gap` lifts the same printed-data contrast to the infinity norm; and `cramerGeppExample_scaledResidual_vecNorm2Sq_gap` gives the squared 2-norm version. Still open: reconstruct the hidden MATLAB matrix/RHS, exact solution, and `K_2(A)` provenance if that generation path is required; raw residuals are not printed in the source table. |
| C1F.7 | §1.11--§1.13 | Accumulation, pivoting, square-root/squaring, infinite-sum, and precision-increase examples. | The `(1 + 1/n)^n` single-rounding amplification, Problem 1.5 exact/log-error and supplied rounded-outer-exp layers, §1.12.1 no-pivot and concrete pivoted IEEE-single examples, §1.12.2 exact square-root/squaring baseline and HP 48G surrogate, and §1.13 exact sine/branch substrates are partly closed by the named theorems in the line-by-line ledger. For §1.13 specifically, `increasingPrecisionSinExampleSource_finiteRoundToEven_eq_base_of_spacing` closes the compact finite-format spacing-certificate theorem for the sine plateau: a finite `x` separated from every other finite value by more than `2*10^{-8}` rounds `x+10^{-8}sin(2^24*x)` back to `x`. The concrete IEEE-single base-point theorem `increasingPrecisionSinExampleSource_ieeeSingle_roundToEven_one` instantiates this local plateau at `x = 1` using the adjacent binary32 endpoints around `1`; `one_seventh_not_binaryTerminating`, `one_seventh_not_ieeeSingleFiniteSystem`, and `one_seventh_not_ieeeDoubleFiniteSystem` close the finite-storage obstruction behind the source's `x = 1/7` representation sentence; `increasingPrecision_ieeeSingle_roundToEven_one_seventh`, `increasingPrecision_ieeeDouble_roundToEven_one_seventh`, `increasingPrecision_ieeeSingle_roundToEven_one_seventh_error`, and `increasingPrecision_ieeeDouble_roundToEven_one_seventh_error` identify the corresponding round-to-even stored values and exact representation errors as `9586981*2^-26` with error `3/(7*2^26)` and `5146971002709138*2^-55` with error `-2/(7*2^55)`; and `increasingPrecision_one_seventh_binary_grid_abs_error_ge` plus `increasingPrecision_one_seventh_binary_grid_abs_error_gt_scale_of_t_le_twenty` prove uniformly that every dyadic grid value `z/2^t` is at least `1/(7*2^t)` away from `1/7`, hence farther than the source amplitude `10^-8` whenever `t <= 20`. Also, `increasingPrecisionExampleY_ne_zero_of_ne_two_thirds`, `increasingPrecisionExampleY_pos_of_ne_two_thirds`, and `increasingPrecisionExampleElse_two_precision_failure_of_stored_inputs_expHat_one` close the compact stored-input branch bridge: any stored input not exactly `2/3` enters the else branch, and two such supplied `exp(y)=1` runs both return `0` with relative error `1`; the concrete correctly rounded finite-selector version is closed by `increasingPrecisionExampleElse_two_precision_failure_of_ieee_roundToEven_stored_exp_source`, which supplies the single/double stored values, branch variables, and finite round-to-even exponential values internally. For §1.12.3 specifically, the inverse-square term-size/tail substrate is closed by `inverseSquareTerm_pos_of_pos` and `inverseSquareTerm_le_two_pow_neg_24_of_ge`; the reusable local successor lemma is `inverseSquareSingle_add_term_rounds_to_next_of_half_ulp_lt`; the early-prefix integer sum, bounded nearest-increment certificate, source-rounding bridge, and first-step bridge are closed by `inverseSquareSingleEarlyMantissaPrefix_2895_eq`, `inverseSquareSingleEarlyMantissaPrefix_2895_add_base_eq_preWindow`, `inverseSquareSingleEarlyMantissaIncrementNearestCertificate`, `inverseSquareSingle_add_term_rounds_to_nearest_mantissa_of_scaled_bounds`, `inverseSquareSingleEarlyMantissaIncrementRule_closed`, `inverseSquareSingleForwardAccumulator_one_eq_one`, and `inverseSquareSingleForwardAccumulator_2896_eq_prePlateauWindowStart`; the non-enumerative 2897--4090 intermediate window, 4091--4095 intermediate tail, actual 2897--4095 below-plateau theorem, and actual 4096-and-after plateau theorem are closed by `inverseSquareSingleForwardAccumulatorFrom_prePlateauWindowStart_2897_of_le_1194`, `inverseSquareSingleForwardAccumulatorFrom_sixBeforePlateau_4091_of_le_5`, `inverseSquareSingleForwardAccumulatorFrom_prePlateauWindowStart_2897_lt_plateau_of_lt_1200`, `inverseSquareSingleForwardAccumulator_2896_add_lt_plateau`, and `inverseSquareSingleForwardAccumulator_4096_add_eq_plateau`; the local binary32 predecessor, plateau-entry, and post-plateau drop-off mechanisms are closed by `inverseSquareSingleSixBeforePlateau_add_4091_term_rounds_to_fiveBeforePlateau`, `inverseSquareSingleFiveBeforePlateau_add_4092_term_rounds_to_fourBeforePlateau`, `inverseSquareSingleFourBeforePlateau_add_4093_term_rounds_to_threeBeforePlateau`, `inverseSquareSingleThreeBeforePlateau_add_4094_term_rounds_to_twoBeforePlateau`, `inverseSquareSingleTwoBeforePlateau_add_4095_term_rounds_to_prePlateau`, `inverseSquareSinglePrePlateau_add_4096_term_rounds_to_plateau`, `inverseSquareSinglePlateau_add_4096_term_rounds_to_self`, `inverseSquareSinglePlateau_add_positive_term_le_two_pow_neg_24_rounds_to_self`, and `inverseSquareSinglePlateau_add_term_rounds_to_self_of_ge_4096`; and the reverse-order loop shape is now modeled by `inverseSquareSingleReverseAccumulatorFrom`, `inverseSquareSingleReverseAccumulator`, `inverseSquareSingleReverseAccumulatorFrom_add`, and `inverseSquareSingleReverseAccumulator_ten_pow_nine_split_4096`. Still open: a concrete Fortran execution derivation of Table 1.1, concrete libm/IEEE exp/log routine contracts for Problem 1.5, a Strassen empirical threshold-error-growth theorem beyond the closed dominant multiplication-count substrate, the instantiation of the HP 48G root/square phase laws from a concrete calculator model, the reported reverse-order `10^9` summation value and related summation-order examples, an unspecified vendor Fortran/libm derivation for §1.13 if required beyond the repository's correctly rounded finite selector model, the Hilbert/Pascal precision plots, the rest of the local spacing-certificate instantiations for the displayed binary-rounding plateau interval of `x+a sin(bx)`, the displayed `-8.55e-9` sine perturbation value, and §1.13 monotonicity/precision-relationship caveats beyond the supplied two-run bridge. |

C1F.7 correction: the §1.13 dyadic `1/7` dominance sentence in the broad row
above is superseded by the addendum below. The sharpened threshold theorem is
`increasingPrecision_one_seventh_binary_grid_abs_error_gt_scale_of_t_le_twenty_three`;
the direct perturbation theorem is
`increasingPrecisionSinExampleSource_perturbation_lt_one_seventh_binary_grid_error_of_t_le_twenty_three`;
and `increasingPrecision_one_seventh_binary_grid_lower_bound_lt_scale_at_twenty_four`
records that the universal lower-bound comparison has already flipped at
`t = 24`.
| C1F.7 addendum | §1.13 `x = 1/7` early dyadic-grid dominance | `increasingPrecision_one_seventh_binary_grid_abs_error_ge` proves every dyadic grid value `z/2^t` is separated from exact `1/7` by at least `1/(7*2^t)`, `increasingPrecision_one_seventh_binary_grid_abs_error_gt_scale_of_t_le_twenty_three` proves this lower bound exceeds the source sine amplitude `10^-8` for every `t <= 23`, and `increasingPrecisionSinExampleSource_perturbation_lt_one_seventh_binary_grid_error_of_t_le_twenty_three` composes the two facts to show the sine perturbation is smaller than the input-representation error throughout that sharpened early-precision range. The conservative `t <= 20` theorem remains available for the source's "less than about 20" wording, and `increasingPrecision_one_seventh_binary_grid_lower_bound_lt_scale_at_twenty_four` records that the universal lower-bound comparison has already flipped at `t = 24`. This is a uniform arithmetic theorem, not a replay of the plotted `t = 10:40` data. Still open: the displayed sine perturbation decimal and the full `22 < t < 31` plateau instantiation. |
| C1F.7 addendum | §1.11 single-rounded-base amplification | `expOneApproxRoundedBase_relError_eq_initial_error_pow_abs` now closes the exact relative-error form of the source's single-initial-rounding warning: for every `n`, if `1+1/n` is first rounded by the `FPModel` addition contract and the rounded base is then exponentiated exactly, the relative error against `(1+1/n)^n` is exactly `|(1+delta)^n - 1|` for some `|delta| <= fp.u`. This is a uniform symbolic theorem, not a case-by-case Table 1.1 replay; the concrete Fortran Table 1.1 execution and named power/libm contracts remain open. |
| C1F.7 addendum | §1.11 Problem 1.5 finite round-to-even exp/log wrapper | `expOneApproxLogExpFiniteRoundToEven_exists_contract_of_finiteNormalRange` and `expOneApproxLogExpFiniteRoundToEven_relError_le_fp_of_finiteNormalRange` now close the finite-normal round-to-even instantiation of the supplied logarithm and outer-exponential relative-error variables in Problem 1.5. Under `fmt.unitRoundoff <= fp.u` and finite-normal range hypotheses for `log(1+1/n)` and the exact outer exponential after the rounded log, Lean proves the concrete finite-round-to-even log-exp route has relative error at most `exp(fp.u)*(1+fp.u)-1` against `(1+1/n)^n`. The scalar bound is also closed as a literal first-order statement by `expOneApproxLogExpUnitRoundoffEnvelope_isBigO`, proving `exp(u)*(1+u)-1 = O(u)` as `u -> 0`. This narrows the remaining §1.11 routine gap to a named libm/IEEE or Fortran execution derivation beyond the finite round-to-even selector. |
| C1F.7 addendum | §1.12.2 HP 48G surrogate law bridge | `hp48gSqrtSquareTrace_eq_surrogate_of_laws` now closes the derivation of Higham's displayed step surrogate from compact phase laws. It assumes the 60-square-root phase rounds `x >= 1` to `1`, maps `0 <= x < 1` into `[0, hp48gTwelveDigitBelowOne]`, and that the 60-squaring phase fixes `1` while underflowing that interval to `0`; under those laws, the composed trace is exactly `hp48gSqrtSquareSurrogate` for every nonnegative input. This deliberately avoids a 120-operation or thousands-case proof. Still open: instantiate those phase laws from a concrete HP 48G decimal range, rounding-to-one, and underflow model. |
| C1F.7 addendum | §1.12.1 no-pivot representable-inverse threshold | The no-pivot inverse update now has a compact finite-format binade theorem beyond the concrete `epsilon=2^-24` midpoint: `noPivotIeeeSingle_add_one_normalized_rounds_to_self_of_two_lt_ulp` proves that adding `1` to a positive IEEE-single normalized value rounds back to that value whenever the binade ulp is greater than `2`, `noPivotIeeeSingle_add_one_normalized_rounds_to_self_of_exp_ge_26` specializes this to every representable inverse in exponent binade at least `26`, and `noPivotIeeeSingle_add_one_inv_rounds_to_inv_of_inv_normalized_exp_ge_26` states the same fact as `fl(1+epsilon^{-1})=epsilon^{-1}`. The ulp-`2` midpoint layer is classified by `noPivotIeeeSingle_add_one_normalized_rounds_to_self_of_ulp_eq_two_even`, `noPivotIeeeSingle_add_one_normalized_rounds_to_succ_of_ulp_eq_two_odd`, the exponent-25 wrappers, and the max-mantissa carry endpoint theorem. The concrete exponent-26 names remain available as specializations. This is a representable-inverse theorem, not an enumeration of cases; the source-facing finite-output guard is closed by `noPivotIeeeSingle_add_one_inv_rounds_to_inv_requires_inv_finiteSystem` and `noPivotIeeeSingle_add_one_inv_not_rounds_to_inv_of_inv_not_finiteSystem`, so arbitrary real `epsilon` cannot satisfy exact equality unless `epsilon^{-1}` is finite-format and in one of the classified left-rounding cases. |
| C1F.7 addendum | §1.12.1 pivoted all-small IEEE-single thresholds | The pivoted finite-format primitive facts are now closed without case enumeration by `noPivotIeeeSingle_partialPivot_div_epsilon_one_rounds_to_epsilon_of_finiteSystem`, `noPivotIeeeSingle_partialPivot_mul_epsilon_one_rounds_to_epsilon_of_finiteSystem`, `noPivotIeeeSingle_add_one_epsilon_rounds_to_one_of_nonneg_le_small`, and `noPivotIeeeSingle_partialPivot_sub_neg_one_epsilon_rounds_to_neg_one_of_nonneg_le_small`. These discharge the finite `epsilon/1` and `epsilon*1` exactness facts for finite IEEE-single values and the `0 <= epsilon <= 2^-24` pivoted rounding thresholds `fl(1+epsilon)=1` and `fl((-1)-epsilon)=-1`. The no-pivot real-`epsilon` representability guard is closed by `noPivotIeeeSingle_add_one_inv_rounds_to_inv_requires_inv_finiteSystem` and `noPivotIeeeSingle_add_one_inv_not_rounds_to_inv_of_inv_not_finiteSystem`, so arbitrary real `epsilon` cannot satisfy the no-pivot exact-equality premise unless `epsilon^{-1}` is finite-format. |
| C1F.7 addendum | §1.12.3 reverse inverse-square summation | The reverse-order `10^9` printed-value route now has exact-prefix, error-radius, and rational lower-bound transfer theorems. `inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixWindow_of_eq_exact`, `inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow_of_eq_exact`, `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_eq_exact`, and `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_eq_exact_tight` prove that if the rounded high-index prefix equals the exact high-prefix sum, the exact telescoping window bounds place the rounded state in the suffix-start window and the final reverse value follows from the matching suffix-window certificate. More realistically, `inverseSquareSingleReverseHighPrefixTightWindowMargin`, `inverseSquareSingleReverseHighPrefixTightWindowMargin_nonneg`, `inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow_of_abs_error_le_margin`, and `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_abs_error_le_margin` prove that an explicit absolute-error bound from the rounded high-prefix state to the exact high-prefix mass is sufficient for the refined tight-window route. The concrete layer `inverseSquareSingleReverseHighPrefixTightWindowMarginLowerBound`, `inverseSquareSingleReverseHighPrefixTightWindowMarginLowerBound_nonneg`, `inverseSquareSingleReverseHighPrefixTightWindowMarginLowerBound_le_margin`, `inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow_of_abs_error_le_marginLowerBound`, and `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_abs_error_le_marginLowerBound` replaces that exact-margin target by a fully explicit rational telescoping slack. The sharper shifted layer `inverseSquareSingleReverseHighPrefixTightWindowMarginShiftedLowerBound`, `inverseSquareSingleReverseHighPrefixTightWindowMarginShiftedLowerBound_le_margin`, `inverseSquareSingleReverseTenPowNineHighPrefixCandidate_abs_error_le_shiftedMarginLowerBound`, `inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow_of_abs_error_le_shiftedMarginLowerBound`, and `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_abs_error_le_shiftedMarginLowerBound` replaces the overly conservative coarse slack with a near-half-shifted telescope that contains the concrete high-prefix candidate. The candidate-window layer `inverseSquareSingleReverseHighPrefixCandidateWindowLower`, `inverseSquareSingleReverseHighPrefixCandidateWindowUpper`, `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow`, `inverseSquareExactReverseTenPowNineHighPrefix_mem_candidateWindow`, `inverseSquareSingleReverseHighPrefixCandidateWindow_mem_printedSuffixStartTightWindow`, `inverseSquareSingleReverseCandidateWindowMapsToPrinted`, and `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_candidateWindow_certificates` packages the remaining rounded-prefix and final-suffix obligations into the same 1024-ulp binary32 window around the candidate. The first interval transition inside that suffix map is closed by `inverseSquareSingleReverseCandidateWindow_add_4096_term_mem_after4096Window` and `inverseSquareSingleReverseCandidateWindow_round_4096_step_mem_after4096Window`: exact addition of `4096^{-2}` maps the candidate window into a 512-ulp post-`4096` window, and nearest-finite endpoint enclosure keeps the rounded first suffix step inside that post-window. Later window-band and final before-`4` entries close the whole candidate-window suffix map by `inverseSquareSingleReverseCandidateWindowMapsToPrinted_closed`. The finite-cell guard layer adds `inverseSquareSingleReverseHighPrefixCandidateWindowLowerPred`, `inverseSquareSingleReverseHighPrefixCandidateWindowUpperSucc`, `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuard`, `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_cellGuard`, and `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_candidateWindowCellGuard_closed`, reducing the remaining high-prefix proof to two strict inequalities around the candidate-window endpoints once finite-system membership is known. The stricter cell-margin layer adds `inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound`, `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget`, `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_abs_error_lt_cellGuardMarginShiftedLowerBound`, `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_cellGuardMarginTarget`, and `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_cellGuardMarginTarget_closed`, so the remaining proof can be targeted as one strict absolute-error certificate against a predecessor/successor-cell margin that is larger than the earlier closed-window margin. Still open: prove the actual rounded high-prefix state satisfies this strict cell-margin target; the low-index suffix case split is closed and was handled by chunk/window certificates, not enumeration. |
| C1F.7 addendum | §1.12.3 current reverse suffix frontier | Reverse inverse-square suffix frontier. | Later 2026-06-13 window-band and final before-`4` entries supersede the older before-`2048` and before-`8` statuses in the preceding reverse-summation addendum. The candidate-window suffix route is now closed by `inverseSquareSingleReverseCandidateWindowMapsToPrinted_closed`, and the printed-value theorem is closed under the high-prefix candidate-window hypothesis by `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_mem_candidateWindow_closed`. The only remaining reverse-order frontier is rounded high-prefix membership `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow`. It is reducible to the named closed-window absolute-error proposition `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowMarginTarget`, to the strict finite-cell guard `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuard`, or more sharply to the single strict cell-margin proposition `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget`. The old closed-window target implies the strict cell-margin target by `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget_of_candidateWindowMarginTarget`; the observed candidate satisfies the strict margin by `inverseSquareSingleReverseTenPowNineHighPrefixCandidate_abs_error_lt_cellGuardMarginShiftedLowerBound`; equality to the observed candidate implies the strict target by `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget_of_eq_candidate`; and that strict target closes the printed-value theorem via `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_cellGuardMarginTarget_closed`. The standard-error envelope is now wired into this route by `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowMarginTarget_of_stdErrorEnvelope_le`, `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget_of_stdErrorEnvelope_lt`, and the two printed-value wrappers with suffixes `_stdErrorEnvelope_le_candidateWindowMargin_closed` and `_stdErrorEnvelope_lt_cellGuardMargin_closed`; proving a genuinely sharp envelope/cell bound would close the same D1 frontier. The `8192` split foothold now adds `inverseSquareTerm_le_two_pow_neg_26_of_reverse_ten_pow_nine_high_binade`, `inverseSquareSingleReverseTenPowNineHighPrefixState_split_8192`, `inverseSquareExactReverseTenPowNineHighPrefix_split_8192`, `inverseSquareExactReverseTenPowNineHighPrefixBefore8192_le_inv_8192`, `inverseSquareSingleReverseTenPowNineHighPrefixBefore8192_le_inv_4096`, `inverseSquareExactReverseBinade8192To4097_le_inv_8192`, and `inverseSquareSingleReverseBinade8192To4097_le_start_add_inv_4096`, reducing the next route to a blockwise high-prefix interval/cell certificate over `10^9, ..., 8193` and `8192, ..., 4097` with an earlier-block rounded start bound of `1/4096` and a final-binade rounded increment budget of `1/4096`. The guard `inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound_lt_inv_4096` proves that coarse budget is still larger than the strict finite-cell margin, so it cannot be used directly as the final D1 certificate. The next proof step is therefore a sharper compact high-prefix interval/cell certificate, not a replay of the 4096 low-index suffix proof. |
| C1F.8 | §1.14.1 | Algorithms for `(e^x - 1)/x` and the roughly `3.5u` bound. | Exact Algorithm 1/2 branch definitions and their exact equivalence are closed by `expm1Algorithm2Exact_eq_algorithm1Exact`; Table 1.2's displayed `x`, Algorithm 1, Algorithm 2, missing final-entry, and `10^-15` correction-note data are closed by `expm1Table12_x_rows`, `expm1Table12_algorithm1_rows`, `expm1Table12_algorithm2_rows`, and `expm1Table12_algorithm2_ten_pow_neg15_last_digit_correction`; the page-23 displayed ratio lines are closed by `expm1Page23_displayed_single_precision_ratio` and `expm1Page23_displayed_exact_arithmetic_ratio`; the removable singularity of the slow ratio is closed by `expm1LogRatio_tendsto_one`; the page-24 denominator Taylor/remainder/reciprocal expansion is closed by `expm1Log_one_add_sub_linear_quadratic_abs_le`, `expm1LogRatioDenRemainder_abs_le`, and `expm1LogRatio_one_add_eq_inv_one_sub_half_add_remainder`; the page-24 `g(1+v)=1+v/2+O(v^2)` expansion plus `g(y)` close-to-one/self bounds are closed by `expm1LogRatio_one_add_sub_one_add_half_abs_le`, `expm1LogRatio_sub_one_abs_le`, and `expm1LogRatio_self_sub_abs_le`; the exact two-point comparison substrate `g(yhat)-g(y) ≈ (yhat-y)/2` is closed by `expm1LogRatio_one_add_diff_sub_half_abs_le`; the rounded-exponential substitutions to `y*delta/2`, `delta/2`, and `g(y)*delta/2` are closed by `expm1LogRatio_mul_one_add_delta_diff_sub_y_delta_half_abs_le`, `expm1LogRatio_mul_one_add_delta_diff_sub_delta_half_abs_le`, and `expm1LogRatio_mul_one_add_delta_diff_sub_logRatio_delta_half_abs_le`; the source equation (1.9) algebra is closed by `expm1Algorithm2RoundedCore_eq_source_1_9`; the exact-subtraction, guard-digit-model, and finite-round-to-even/Ferguson refinements `expm1Algorithm2RoundedCore_eq_source_1_9_of_exact_sub`, `expm1Algorithm2RoundedCore_eq_source_1_9_of_guardDigitSubtractionModel`, and `expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_ferguson` close the `epsSub = 0` path under their explicit hypotheses; a generic `gamma_4` bridge to the slow ratio `g(yhat)` is closed by `expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma4`. The rounded-exp finite-output and finite-normal `delta` adapters discharge `yhat` finite representability and `|delta| <= fp.u` from `yhat = finiteRoundToEven(exp x)` plus the normal-range/unit-roundoff hypotheses, the rounded-log finite-normal adapter discharges the supplied `epsLog`, `logHat != 0`, and `0 < 1+epsLog` hypotheses from `logHat = finiteRoundToEven(log yhat)`, and the routine-link wrappers replace the pointwise subtraction equality by `finiteRoundToEvenSubtractionLink fp fmt`. The sharper source-shaped `3.5u` bridge is now closed under finite-normal rounded-exp/log hypotheses by `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_log_finiteNormal` and its source-function target version `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_log_finiteNormal_algorithm1Exact`. Still open: concrete exp/log finite-normal/routine instantiation, proof of the routine-level subtraction link for the selected machine model where exact finite-format subtraction is required, and machine-specific MATLAB/IEEE derivation of the Table 1.2 computed columns. |
C1F.8 Sterbenz update: `expm1Algorithm2_yhat_one_sterbenzRatioCondition_of_abs_sub_one_le_third`
and
`expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_sterbenz_radius`
close the local-radius route to exact finite round-to-even subtraction for
`yhat - 1`: finite representability plus `|yhat-1| <= 1/3` is enough to set
`epsSub = 0`, avoiding pointwise Ferguson case enumeration on the small-`x`
path. The source-shaped wrappers
`expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_exp_perturb_sterbenz_radius`,
`expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_exp_x_sterbenz_radius`,
and
`expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_exp_x_mul_one_add_u_sterbenz`
derive this local radius from the PDF's rounded-exponential hypotheses instead
of from any per-exponent case split. The exact-subtraction facts
`expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_sterbenz_radius`,
`expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_perturb_sterbenz_radius`,
`expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_x_sterbenz_radius`,
and
`expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_x_mul_one_add_u_sterbenz`
now expose `fp.fl_sub yhat 1 = yhat - 1` directly, and the
`expm1Algorithm2RoundedCore_*gamma2*` theorems charge only the rounded log and
final division factors on this exact-subtraction path. The finite-output
lemmas for `finiteRoundToEven`, `finiteRoundToEvenOp`, and
`finiteRoundToEvenSqrt` expose source-facing round-to-even results as finite
representable, and the rounded-exp-produced wrappers with suffix
`_rounded_exp_x_mul_one_add_u_sterbenz` discharge the `yhat` finite hypothesis
from `yhat = finiteRoundToEven(exp x)`. The finite-normal adapter
`expm1Algorithm2RoundedExp_delta_abs_le_of_finiteNormalRange` and wrappers with
suffix `_exp_finiteNormal_sterbenz` additionally derive the rounded-exp
`|delta| <= fp.u` hypothesis from the finite-normal round-to-even contract. The
rounded-log adapter `expm1Algorithm2RoundedLog_exists_contract_of_finiteNormalRange`
and wrappers with suffix `_exp_log_finiteNormal_sterbenz` also derive the
rounded-log witness and side conditions from finite round-to-even `log yhat`.
The predicate `finiteRoundToEvenSubtractionLink` and wrappers with suffix
`_of_subtractionLink` lift the remaining subtraction operation equality from a
pointwise produced-`yhat` hypothesis to a single routine-level link.
| C1F.9 | §1.14.2 | Chapter 1 QR example bridge. | Exact orthogonality of the displayed embedded Givens block is closed by `givensRotation_trig_orthogonal`; exact component action and ratio zeroing are closed by `givensRotation_mulVec_p`, `givensRotation_mulVec_q`, `givensRotation_ratio_zeroes_q`, and `givensRotation_ratio_mulVec_p`; and the source zeroing-schedule count is closed by `givensQRRectangularRotationCount_twice_int` plus the `10 x 6` corollary `givensQRRectangularRotationCount_ten_by_six = 39`. Still open: formalize the worked numerical QR example's hidden matrix/intermediate data and instantiate the bridge to existing Givens/Householder QR backward-error and QR perturbation theorems. |
| C1F.10 | §1.15--§1.17 | Beneficial rounding, problem-dependent stability, and nonrandom rounding examples. | The exact §1.15 eigenvalue line, terminating-binary and IEEE-double exact-storage obstruction, zero-step, first-step perturbation substrate, inverse-iteration shifted-system/eigenvector substrate, and conditional harmless-direction substrate are partly closed by the named `BeneficialRounding.lean` theorems in the line-by-line ledger. The §1.16 upper-Hessenberg determinant substrate, printed Table 1.3 data layer, residual contrast, determinant accuracy, and first-multiplier fact are partly closed by the named `ProblemDependentStability.lean` theorems. The exact §1.17 Kahan rational-function/grid setup, continued-fraction reference layer, abstract rounded-Horner local-error expansion, IEEE-double source-grid local-error expansion, and selected-pair stored-input Figure 1.6 diagnostic are closed by `NonrandomRounding.lean`; in particular `exists_ieeeDoubleKahanStoredGridRationalFunction_grid_error_spread_gt_one_e13` proves two valid stored-input source-grid errors differ by more than `10^-13`, and `not_forall_ieeeDoubleKahanStoredGridError_eq_on_source_grid` proves the modeled grid-error sequence is not constant. Full reproduction of all 361 plotted markers is classified as optional artifact generation rather than a remaining theorem-level gap. Still open: concrete perturbation size and convergence for the MATLAB power-method observation, now tracked as the dedicated bottleneck `docs/CHAPTER01_BENEFICIAL_POWER_METHOD_BOTTLENECK.md` and proof-source chain `C1.15-BPM` in `docs/CHAPTER01_PROOF_SOURCE_LEDGER.md`; the cited inverse-iteration perturbation theorem supplying the near-parallel solve-error hypothesis and a concrete shifted-solve floating-point trace; and source attribution or a primitive-operation single-precision derivation for the hidden §1.16 Table 1.3 solve convention. |
| C1F.10 addendum | §1.15 two-component power-method convergence-rate substrate | `powerMethodIterate_two_eigencomponents` proves that a two-eigencomponent starting vector evolves by scaling each component by the corresponding eigenvalue power after `k` unnormalized power-method steps. `powerMethod_component_abs_ratio_eq_initial_mul_spectral_ratio`, `powerMethod_component_abs_ratio_le_geometric_of_spectral_ratio_le`, and `powerMethod_component_abs_ratio_tendsto_zero_of_spectral_ratio_lt_one` prove the exact scalar ratio formula, a geometric `q^k` bound from a supplied spectral-ratio bound, and convergence of the non-dominant/dominant ratio to zero when the spectral ratio is strictly below one. This closes a compact, non-enumerative formal version of the §1.15 "theory says" linear-rate explanation for the two-component case. Remaining open at this layer is not another component-by-component proof, but the concrete eigen-decomposition and perturbation data for the stored `A+DeltaA`, the hidden MATLAB/BLAS first-step and printout trace, and the 38-iteration observation. |
| C1F.10 addendum | §1.15 finite-tail power-method convergence bridge | `matMulVec_fin_sum_right` supplies the matrix-vector finite-sum distribution helper, `vecNorm2_finset_sum_le` and `vecNorm2_fin_sum_le` supply the finite-sum Euclidean triangle inequalities, and `powerMethodIterate_dominant_plus_finite_tail` proves that a dominant eigencomponent plus any finite non-dominant tail evolves by scaling each component by its eigenvalue power after `k` unnormalized power-method steps. `powerMethod_finite_tail_abs_sum_ratio_le_geometric_of_spectral_ratio_le`, `powerMethod_finite_tail_geometric_bound_tendsto_zero`, and `powerMethod_finite_tail_abs_sum_ratio_tendsto_zero_of_geometric_bound` prove the aggregate finite-tail coefficient `q^k` bound and convergence to zero under a common spectral-ratio bound `0 <= q < 1`; `powerMethod_finite_tail_vecNorm2_ratio_le_geometric_of_spectral_ratio_le` and `powerMethod_finite_tail_vecNorm2_ratio_tendsto_zero_of_geometric_bound` prove the corresponding Euclidean-norm tail bound and convergence. `powerMethodIterate_dominant_scaled_residual_ratio_le_geometric_of_finite_tail` and `powerMethodIterate_dominant_scaled_residual_tendsto_zero_of_finite_tail` lift this to the actual power-method iterate: after subtracting the dominant component and scaling by the dominant scalar magnitude, the residual norm is geometrically bounded and tends to zero. `PowerMethodDominantFiniteTailCertificate.scaled_residual_tendsto_zero` and `beneficialPowerStoredStart_dominant_component_certificate_scaled_residual_tendsto_zero` now package the exact certificate-to-convergence handoff for the stored §1.15 matrix/start vector. This closes the finite-family power-method theory bridge and its concrete handoff non-enumeratively. Remaining open: construct a suitable eigencomponent certificate for the concrete stored matrix `A+DeltaA`, prove the dominant eigenpair perturbation facts, identify or assume the hidden MATLAB/BLAS matvec trace, and prove the 38-iteration observation. |
| C1F.10 addendum | §1.17 Kahan stored-grid error nonconstancy | `ieeeDoubleKahanStoredGridError` names the stored-input IEEE-double error sequence, `exists_ieeeDoubleKahanStoredGridError_pair_spread_gt_one_e13` preserves the selected-pair `> 10^-13` spread in that notation, and `not_forall_ieeeDoubleKahanStoredGridError_eq_on_source_grid` proves the sequence is not constant over the valid source grid. This uses one certified pair and does not enumerate all 361 points. Since the source's mathematical conclusion is that the errors are not random, this closes the theorem-level §1.17 nonrandomness obligation; reproducing every plotted marker of Figure 1.6 is optional artifact work. |
| C1F.10 addendum | §1.15 inverse-iteration near-parallel residual bridge | The §1.15 inverse-iteration bridge now includes `eigenResidualVec`, `eigenResidualVec_add_parallel_eq`, `eigenResidualVec_norm_le_opNorm_add_abs`, `inverseIteration_near_parallel_error_eigenResidual_eq`, and `inverseIteration_near_parallel_error_eigenResidual_norm_le`. These theorems prove in one generic step that a shifted-solve error `eta*x + r` leaves only `r` in the eigen-residual, with the norm bound `(A_norm + |lambda|)*||r||_2` under `opNorm2Le A A_norm`. The displayed Higham matrix/start-vector specialization is also exposed as `beneficialPower_inverseIteration_near_parallel_error_eigenResidual_eq`, `beneficialPower_inverseIteration_near_parallel_error_eigenResidual_norm_le`, `beneficialPower_inverseIteration_near_parallel_error_eigenResidual_norm_le_of_residual_norm_le`, and `beneficialPower_inverseIteration_near_parallel_error_eigenResidual_norm_le_of_componentwise_common_scalar`; for `lambda=0`, this gives the concrete §1.15 residual bounds `A_norm*||r||_2`, `A_norm*eps`, and `A_norm*(sqrt 3*eps)` from componentwise closeness to a common scalar. This is the compact theorem/certificate route, not a case-by-case proof of finite inputs. Still open: the concrete rounded shifted-solve trace and the cited perturbation theorem, now sharpened to the obligation of supplying this componentwise/common-direction certificate or an equivalent near-parallel decomposition. |
| C1F.10 addendum | §1.15 perturbed power-method restart norm bridge | `beneficialPowerFirstStep_perturbed_eq_zero_iff_row_sums_zero` and `beneficialPowerFirstStep_perturbed_vecNorm2_eq_zero_iff_row_sums_zero` now characterize the displayed first perturbed step exactly: the vector and its Euclidean norm vanish iff every stored-perturbation row sum vanishes. `beneficialPowerFirstStep_perturbed_vecNorm2_pos_of_delta_row_sum_ne_zero` lifts a nonzero row sum to positive norm, `beneficialPowerFirstStep_perturbed_vecNorm2_ge_of_row_sum_abs_ge` gives a row-sum lower-bound certificate, and the budget adapters `beneficialPowerFirstStep_perturbed_vecNorm2_le_of_row_sum_abs_le` and `beneficialPowerFirstStep_perturbed_vecNorm2_le_of_entry_abs_le` quantify the same first step from above: row-sum radius `eps` gives norm at most `sqrt 3*eps`, and entrywise radius `eps` gives norm at most `sqrt 3*(3*eps)`. The concrete IEEE-double entrywise-storage first-step vector is now closed by the fraction rounding theorems from `1/10` through `7/10`, `ieeeDoubleFormat_one_half_rounds_to`, `beneficialPowerMatrixIeeeDoubleRounded_row_zero_sum_eq`, `beneficialPowerMatrixIeeeDoubleRounded_row_one_sum_eq`, `beneficialPowerMatrixIeeeDoubleRounded_row_two_sum_eq`, `beneficialPowerMatrixIeeeDoubleRounded_firstStep_eq`, and `beneficialPowerMatrixIeeeDoubleRounded_firstStep_abs_between_one_e17_one_e16`: the unnormalized rounded first step is exactly `[2^-54, -2^-54, -2^-55]^T`, every component has magnitude between `10^-17` and `10^-16`, and the rounded first-step norm is at least `2^-54`. Remaining open: a hidden MATLAB primitive-operation/BLAS matvec and printout trace if that exact implementation path is required, the 38-iteration observation, and dominant-eigenpair perturbation theory for the rounded matrix. |
| C1F.10 addendum | §1.15 left-to-right rounded-add operation-order caveat | `beneficialPowerMatrixIeeeDoubleRoundedFirstStepLeftToRight` defines a concrete left-to-right rounded-add row-sum trace after entrywise IEEE-double storage, suppressing only multiplication by the exact start-vector entries `1`. The local rounding facts `ieeeDoubleFormat_half_plus_two_pow_neg55_rounds_to_half` and `ieeeDoubleFormat_neg_half_plus_two_pow_neg55_rounds_to_neg_half` prove the third row's first left-to-right add rounds to exactly `-1/2`; `beneficialPowerMatrixIeeeDoubleRoundedFirstStepLeftToRight_two_component_eq_zero` then proves the third component of this trace is `0`, and `beneficialPowerMatrixIeeeDoubleRoundedFirstStepLeftToRight_ne_firstStep` proves this trace is not the exact entrywise-stored row-sum vector `[2^-54,-2^-54,-2^-55]^T`. This narrows the remaining MATLAB first-step obligation: it is an operation-order/BLAS trace question, not just an entrywise-storage question, and it must not be closed by the exact row-sum theorem alone. |
| C1F.10 addendum | §1.15 right-to-left rounded-add operation-order certificate | `beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft` defines the complementary right-to-left rounded-add row-sum trace after entrywise IEEE-double storage. The component theorems `beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft_zero_component_eq`, `beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft_one_component_eq`, and `beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft_two_component_eq` prove this trace gives exactly `2^-54`, `-2^-54`, and `-2^-55`; `beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft_eq_firstStep` proves the full trace is extensionally equal to the entrywise-storage first-step vector. Together with the left-to-right caveat, this shows that the source-scale first-step vector is reachable by a concrete rounded-add order, but the actual MATLAB/BLAS first-step claim still requires identifying or assuming that operation order. |
| C1F.11 | Problems 1.1--1.10 | Exercises. | Problem 1.1 is closed by the computed-denominator relative-error comparison theorems in `Error.lean`, Problem 1.2 is closed by the finite table-ambiguity theorem in `NearInteger.lean`, Problem 1.3 is closed by exact cancellation-rewrite identities in `TrigCancellation.lean`, Problem 1.4 is closed by exact stable complex-square-root branch formulae in `ComplexSqrt.lean`, Problem 1.6 is closed by exact calculator digit-glyph word theorems in `CalculatorWords.lean`, Problem 1.7 is closed at the first-order finite-difference and displayed closed-form componentwise/normwise condition-number layer in `SampleVariance.lean`, Problem 1.8 is closed at the exact recurrence, qualitative hidden-mode layer, and concrete four-significant-decimal display-trace layer in `MullerRecurrence.lean`, Problem 1.5 is closed at the exact/log-error and supplied rounded-outer-exp composition layers in `Accumulation.lean`, Table 1.1 displayed finite data is closed there as exact rational rows, Problem 1.9 is closed by the denominator-exact Cramer bridge, and Problem 1.10 is closed at the exact perturbed-mean cancellation, relative-error, one-factor rounded-transfer, weighted aggregate-factor bridge, first-pass mean backward/absolute-error, fixed-supplied-mean rounded second-pass, composed explicit-quadratic true-variance relative-error, squared-`gamma fp n` first-pass contribution, and linear `(n+3)u` plus explicit-remainder layers in `SampleVariance.lean`. Still open: full IEEE primitive-operation trace for Problem 1.8 if a named machine path is required, and concrete exp/log routine instantiation plus a concrete Fortran execution derivation of Table 1.1; the literal Problem 1.7 relative-remainder `O(t^2)` theorem and the Problem 1.10 explicit-remainder `O(u^2)` theorem are closed in `SampleVariance.lean`. |
| C1F.11 addendum | Problem 1.8 hidden-mode source-index witness | `mullerModeY_dominates_of_one_le_of_two_le` and `mullerModeRatio_gt_99_of_one_le_of_two_le` prove non-enumeratively that every unit-or-larger hidden-mode contaminant drives the ratio above `99` from `k >= 2`; `mullerModeRatio_lt_100_of_nonneg` proves the contaminated ratio remains below `100` for nonnegative hidden-mode contamination; and `mullerModeRatio_one_34_within_one_of_hundred` specializes these facts at `c = 1`, `k = 34` to prove the hidden-mode ratio is within one unit of `100`. This strengthens the qualitative hidden-mode explanation without changing the remaining open named-machine IEEE primitive-operation trace. |
| C1F.11 addendum | Problem 1.5 finite round-to-even wrapper | The Problem 1.5 exercise layer now includes the finite round-to-even instantiation `expOneApproxLogExpFiniteRoundToEven_relError_le_fp_of_finiteNormalRange`, backed by `expOneApproxLogExpFiniteRoundToEven_exists_contract_of_finiteNormalRange`, plus the literal `O(u)` envelope theorem `expOneApproxLogExpUnitRoundoffEnvelope_isBigO`. The remaining Problem 1.5 exercise gap is therefore a full named libm/IEEE or Fortran trace, not the abstract finite-normal round-to-even relative-error wrapper or the first-order scalar envelope. |

C1F.8 addendum: the §1.14.1 generic `gamma_4` bridge is now also exposed as
the Chapter 1 relative-error theorem `expm1Algorithm2RoundedCore_relError_le_gamma4`.
The definitions `expm1Algorithm2SlowRatioPerturbationBound` and
`expm1Algorithm2LocalRelErrorBound`, together with
`expm1Algorithm2RoundedCore_relError_le_local_bound`, compose the exact
slow-ratio drift for `yhat=y*(1+delta)` with the rounded subtraction/log/division
`gamma_4` factor to give a local bound relative to `g(y)`. The readable
expansion `expm1Algorithm2LocalRelErrorBound_eq_drift_div_add_gamma4` and
certificate consumers `expm1Algorithm2LocalRelErrorBound_le_eta_add_gamma4`
and `expm1Algorithm2RoundedCore_relError_le_eta_add_gamma4` reduce future
instantiations to proving a normalized slow-ratio drift certificate
`drift <= eta*|g(y)|`, after which the bound is
`eta + (1+eta)*gamma_4`. The additional primitive certificate
`expm1Algorithm2PrimitiveDriftBound`, together with
`expm1Algorithm2SlowRatioPerturbationBound_le_of_abs_bounds`,
`expm1Algorithm2LocalDrift_le_primitive_bound`, and
`expm1Algorithm2RoundedCore_relError_le_eta_add_gamma4_of_primitive_bounds`,
reduces the local drift proof to elementary absolute-value budgets for
`|g(y)|`, `|y-1|`, `|yhat-1|`, and `|delta|`. This is still an intermediate
bridge. The signed-product refinement
`expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma3`,
`expm1Algorithm2RoundedCore_relError_le_gamma3`,
`expm1Algorithm2RoundedCore_relError_le_local_bound_gamma3`,
`expm1Algorithm2RoundedCore_relError_le_eta_add_gamma3`, and
`expm1Algorithm2RoundedCore_relError_le_eta_add_gamma3_of_primitive_bounds`
uses the same primitive drift certificate but charges the three local equation
(1.9) factors as `gamma_3`, yielding the source-aligned bound
`eta + (1+eta)*gamma_3`. The corollaries
`expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_remainder` and
`expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_remainder_of_primitive_bounds`
specialize this to `3.5u + ((3u)^2)/(1-3u) + (u/2)*gamma_3` once the drift
budget is at most `(u/2)*|g(y)|`. The local-remainder theorem
`expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_local_remainder_of_abs_bounds`
derives the leading `3.5u` term from `|delta| <= deltaAbs <= u`, leaving the
explicit extra term
`expm1Algorithm2PrimitiveSlowRemainderBound yAbs yhatAbs deltaAbs /
|g(y)| * (1+gamma_3)`. Concrete exp/log routine contracts, finite
representability and finite round-to-even operation links for the actual
rounded `yhat`, Table 1.2 machine derivation, and concrete control of that
remainder remain open; the guard-digit/Ferguson route remains only an
alternate adapter.

C1F.7 addendum: the §1.12.3 successor mechanism is no longer being extended
by proving one predecessor numeral at a time.  The range theorem
`inverseSquareTerm_between_half_ulp_and_one_ulp_of_ge_2897_lt_4096` and wrapper
`inverseSquareSingle_add_term_rounds_to_next_of_index_range` provide the
non-enumerative hook for every `2897 <= k < 4096`; the recursive accumulator
theorem `inverseSquareSingleForwardAccumulatorFrom_normalizedValue_of_index_window`
then packages those steps by induction.  In particular,
`inverseSquareSingleEarlyMantissaPrefix_2895_eq` certifies the integer
mantissa-increment sum for terms `2, ..., 2896`,
`inverseSquareSingleEarlyMantissaPrefix_2895_add_base_eq_preWindow` shows that
this sum lands at the pre-window mantissa,
`inverseSquareSingleEarlyMantissaIncrementNearestCertificate` proves the
strict half-ulp nearest-increment inequalities and mantissa-range bound for
each early term, `inverseSquareSingleForwardAccumulator_one_eq_one`
closes the actual `k = 1` step, and
`inverseSquareSingleForwardAccumulator_2896_eq_prePlateauWindowStart_of_early_mantissa_increment_rule`
reduces the early actual prefix to the uniform local rule
`inverseSquareSingleEarlyMantissaIncrementRule`.  The theorem
`inverseSquareSingle_add_term_rounds_to_nearest_mantissa_of_scaled_bounds`
bridges the finite nearest-increment certificate to the source-rounded binary32
successor step, `inverseSquareSingleEarlyMantissaIncrementRule_closed` closes
the uniform early rule, and
`inverseSquareSingleForwardAccumulator_2896_eq_prePlateauWindowStart` proves
the actual early prefix reaches the pre-window accumulator.  Then
`inverseSquareSingleForwardAccumulatorFrom_prePlateauWindowStart_2897_of_le_1194`
proves every intermediate prefix in the `k = 2897, ..., 4090` window,
`inverseSquareSingleForwardAccumulatorFrom_prePlateauWindowStart_2897_1194_eq_sixBeforePlateau`
proves the endpoint from the pre-window accumulator,
`inverseSquareSingleForwardAccumulatorFrom_sixBeforePlateau_4091_of_le_5`
proves the intermediate `4091`--`4095` tail, and
`inverseSquareSingleForwardAccumulatorFrom_prePlateauWindowStart_2897_lt_plateau_of_lt_1200`
shows the whole `2897`--`4095` window is still below the plateau.  Finally,
`inverseSquareSingleForwardAccumulator_2896_add_lt_plateau` and
`inverseSquareSingleForwardAccumulator_4096_add_eq_plateau` connect those window
theorems to the actual accumulator from zero without an early-rule assumption
and close the left-to-right first-stagnation trace.  The older assumption
wrappers
`inverseSquareSingleForwardAccumulator_2896_add_lt_plateau_of_early_mantissa_increment_rule`,
`inverseSquareSingleForwardAccumulator_4096_add_eq_plateau_of_early_mantissa_increment_rule`,
`inverseSquareSingleForwardAccumulator_4096_add_eq_plateau_of_2896_eq_prePlateauWindowStart`
and
`inverseSquareSingleForwardAccumulator_2896_add_lt_plateau_of_2896_eq_prePlateauWindowStart`
remain available when an external proof directly supplies the pre-window
accumulator equality or the local early-increment rule.  The reverse-order loop
is now named by `inverseSquareSingleReverseAccumulatorFrom` and
`inverseSquareSingleReverseAccumulator`, with
`inverseSquareSingleReverseAccumulator_ten_pow_nine_split_4096` exposing the
source's `10^9`-term run as a high-index prefix followed by the final `4096`
low-index terms.  The high-prefix index lemma
`inverseSquareReverseTenPowNineHighPrefix_index_ge_4097` and term bound
`inverseSquareTerm_le_two_pow_neg_24_of_reverse_ten_pow_nine_high_prefix`
show that every term in that high-index block is at most `2^-24`.  The exact
reverse-prefix accumulator `inverseSquareExactReverseAccumulatorFrom` and exact
split theorem `inverseSquareExactReverseAccumulator_ten_pow_nine_eq_highPrefix_add_low4096`
separate the exact `10^9` reverse sum into the high-index prefix plus the final
`4096` low-index terms.  The telescoping majorant
`inverseSquareTerm_le_telescope` and concrete theorem
`inverseSquareExactReverseTenPowNineHighPrefix_le_inv_4096` prove that the
entire exact real mass of the source's high-index prefix
`10^9, 10^9-1, ..., 4097` is at most `1/4096`, without unfolding or enumerating
the billion-step prefix; equivalently
`inverseSquareExactReverseAccumulator_ten_pow_nine_sub_low4096_le_inv_4096`
proves the exact `10^9` sum exceeds the exact 4096-term reverse tail by at most
`1/4096`.  The binary32 constants
`inverseSquareSingleReversePrintedAccumulator`,
`inverseSquareSingleReverseSuffixStartLower`, and
`inverseSquareSingleReverseSuffixStartUpper` name the printed reverse value
`1.64493406` and the start-window endpoints for the final suffix.  The
telescoping minorant `inverseSquareTerm_ge_telescope_succ` and
`inverseSquareExactReverseAccumulatorFrom_ge_telescope_succ` prove
`1/k - 1/(k+1) <= 1/k^2`, and the concrete start-window theorems
`inverseSquareExactReverseTenPowNineHighPrefix_ge_printedSuffixStartLower`,
`inverseSquareExactReverseTenPowNineHighPrefix_le_printedSuffixStartUpper`,
`inverseSquareExactReverseTenPowNineHighPrefix_mem_printedSuffixStartWindow`,
`inverseSquareExactReverseTenPowNineHighPrefix_le_printedSuffixStartUpperTight`,
`inverseSquareExactReverseTenPowNineHighPrefix_mem_printedSuffixStartTightWindow`,
and
`inverseSquareExactReverseAccumulator_ten_pow_nine_sub_low4096_mem_printedSuffixStartWindow`
squeeze the exact high-index prefix into both the broad and refined tight
suffix-start windows.  The rounded
high-prefix state is named by
`inverseSquareSingleReverseTenPowNineHighPrefixState`.  The concrete candidate
value `inverseSquareSingleReverseTenPowNineHighPrefixCandidate`, corresponding
to IEEE-single bits `0x397ff6b4`, is proved to lie in the same suffix-start
window by
`inverseSquareSingleReverseTenPowNineHighPrefixCandidate_mem_printedSuffixStartWindow`
and in the refined tight window by
`inverseSquareSingleReverseTenPowNineHighPrefixCandidate_mem_printedSuffixStartTightWindow`.
The reusable positive binary32 local rounding bridges
`inverseSquareSingleForwardStep_eq_left_of_adjacent_strict_between_left_closer`
and
`inverseSquareSingleForwardStep_eq_right_of_adjacent_strict_between_right_closer`
factor the finite-normal-range and nearest/even adjacent-bracket reasoning
needed by compact suffix certificates.  The arbitrary-exponent wrapper
`inverseSquareSingleForwardStep_normalizedValue_nearest_mantissa_of_scaled_bounds_at_scale`
turns a same-exponent binary32 suffix step into two integer half-cell
inequalities at scale `2^q`.
The broad final reverse-value certificates are named by
`inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixWindow` and
`inverseSquareSingleReverseSuffixWindowMapsToPrinted`; the refined viable
window route is named by
`inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow` and
`inverseSquareSingleReverseTightSuffixWindowMapsToPrinted`; the concrete candidate
certificates are named by
`inverseSquareSingleReverseTenPowNineHighPrefixEqCandidate` and
`inverseSquareSingleReverseCandidateSuffixMapsToPrinted`.  The composition
theorems
`inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_window_certificates`
and
`inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_mem_window`,
with tight-window counterparts
`inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_tight_window_certificates`
and
`inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_mem_tight_window`,
prove that those certificates imply the source's full `10^9` reverse-order
accumulator equals the binary32 value printed as `1.64493406`; the candidate
variant
`inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_candidate_certificates`
does the same from the concrete equality and suffix trace.  The named
post-`4096` state `inverseSquareSingleReverseAfter4096Candidate` corresponds
to IEEE-single bits `0x3980035a`, and
`inverseSquareSingleReverseCandidate_add_4096_term_rounds_to_after4096` proves
that the first low-index suffix addition is exactly representable and lands on
that state.  The named post-`4095` state
`inverseSquareSingleReverseAfter4095Candidate` corresponds to IEEE-single bits
`0x39800b5b`, and
`inverseSquareSingleReverseAfter4096_add_4095_term_rounds_to_after4095` proves
that the second low-index suffix addition rounds to that state using the
arbitrary-scale certificate with `q = 36`.  The reusable band theorem
`inverseSquareSingleReverseAccumulatorFrom_scaledBandPrefix_of_le` packages the
same-exponent reverse-suffix induction from checked half-cell certificates.  The
first same-exponent after-`4095` band is closed by
`inverseSquareSingleReverseAfter4095Prefix_4094_to_2049_eq`,
`inverseSquareSingleReverseAfter4095Band4094To2049CertificateBool_eq_true`,
`inverseSquareSingleReverseAfter4095Band4094To2049Certificate`, and
`inverseSquareSingleReverseAfter4095Accumulator_4094_to_before2048`, proving
the 2046 additions `4094^{-2}, ..., 2049^{-2}` land on the named
`inverseSquareSingleReverseBefore2048Candidate` state.  The `2048^{-2}`
boundary step is closed by
`inverseSquareSingleReverseBefore2048_add_2048_term_rounds_to_after2048`, which
uses the nearest/even midpoint rule to land on
`inverseSquareSingleReverseAfter2048Candidate` (`0x3a0007a8`).  The next
same-exponent band is closed by
`inverseSquareSingleReverseAfter2048Prefix_2047_to_1025_eq`,
`inverseSquareSingleReverseAfter2048Band2047To1025CertificateBool_eq_true`,
`inverseSquareSingleReverseAfter2048Band2047To1025Certificate`, and
`inverseSquareSingleReverseAfter2048Accumulator_2047_to_before1024`, proving
the 1023 additions `2047^{-2}, ..., 1025^{-2}` land on
`inverseSquareSingleReverseBefore1024Candidate` (`0x3a7fdfb6`).  The theorems
`inverseSquareSingleReverseCandidateSuffixMapsToPrinted_of_after4096`,
`inverseSquareSingleReverseAfter4096SuffixMapsToPrinted_of_after4095`,
`inverseSquareSingleReverseAfter4095SuffixMapsToPrinted_of_before2048`, and
`inverseSquareSingleReverseBefore2048SuffixMapsToPrinted_of_before1024` reduce
the concrete suffix trace to `inverseSquareSingleReverseBefore1024SuffixMapsToPrinted`.
The next exact boundary step is closed by
`inverseSquareSingleReverseBefore1024_add_1024_term_rounds_to_after1024`, landing
on `inverseSquareSingleReverseAfter1024Candidate` (`0x3a800fdb`).  The next
same-exponent band is closed by
`inverseSquareSingleReverseAfter1024Prefix_1023_to_513_eq`,
`inverseSquareSingleReverseAfter1024Band1023To513CertificateBool_eq_true`,
`inverseSquareSingleReverseAfter1024Band1023To513Certificate`, and
`inverseSquareSingleReverseAfter1024Accumulator_1023_to_before512`, proving the
511 additions `1023^{-2}, ..., 513^{-2}` land on
`inverseSquareSingleReverseBefore512Candidate` (`0x3affbfeb`).  The theorem
`inverseSquareSingleReverseBefore1024SuffixMapsToPrinted_of_before512` reduces
the concrete suffix trace further to `inverseSquareSingleReverseBefore512SuffixMapsToPrinted`.
The next boundary/band chunk is also closed:
`inverseSquareSingleReverseBefore512_add_512_term_rounds_to_after512` proves the
`512^{-2}` midpoint-tie step lands on
`inverseSquareSingleReverseAfter512Candidate` (`0x3b001ff6`), and
`inverseSquareSingleReverseAfter512Accumulator_511_to_before256` proves the
compact 255-entry band `511^{-2}, ..., 257^{-2}` lands on
`inverseSquareSingleReverseBefore256Candidate` (`0x3b7f801f`).  The theorem
`inverseSquareSingleReverseBefore512SuffixMapsToPrinted_of_before256` reduces
the concrete suffix trace further to `inverseSquareSingleReverseBefore256SuffixMapsToPrinted`.
The next boundary/band chunk is also closed:
`inverseSquareSingleReverseBefore256_add_256_term_rounds_to_after256` proves the
`256^{-2}` midpoint-tie step lands on
`inverseSquareSingleReverseAfter256Candidate` (`0x3b804010`), and
`inverseSquareSingleReverseAfter256Accumulator_255_to_before128` proves the
compact 127-entry band `255^{-2}, ..., 129^{-2}` lands on
`inverseSquareSingleReverseBefore128Candidate` (`0x3bff00a3`).  The theorem
`inverseSquareSingleReverseBefore256SuffixMapsToPrinted_of_before128` reduces
the concrete suffix trace further to `inverseSquareSingleReverseBefore128SuffixMapsToPrinted`.
The next boundary/band chunk is also closed:
`inverseSquareSingleReverseBefore128_add_128_term_rounds_to_after128` proves the
`128^{-2}` midpoint-tie step lands on
`inverseSquareSingleReverseAfter128Candidate` (`0x3c008052`), and
`inverseSquareSingleReverseAfter128Accumulator_127_to_before64` proves the
compact 63-entry band `127^{-2}, ..., 65^{-2}` lands on
`inverseSquareSingleReverseBefore64Candidate` (`0x3c7e02a3`).  The theorem
`inverseSquareSingleReverseBefore128SuffixMapsToPrinted_of_before64` reduces
the concrete suffix trace further to `inverseSquareSingleReverseBefore64SuffixMapsToPrinted`.
The next boundary/band chunk is also closed:
`inverseSquareSingleReverseBefore64_add_64_term_rounds_to_after64` proves the
`64^{-2}` midpoint-tie step lands on
`inverseSquareSingleReverseAfter64Candidate` (`0x3c810152`), and
`inverseSquareSingleReverseAfter64Accumulator_63_to_before32` proves the
compact 31-entry band `63^{-2}, ..., 33^{-2}` lands on
`inverseSquareSingleReverseBefore32Candidate` (`0x3cfc0aa4`).  The theorem
`inverseSquareSingleReverseBefore64SuffixMapsToPrinted_of_before32` reduces
the concrete suffix trace further to `inverseSquareSingleReverseBefore32SuffixMapsToPrinted`.
The final compact suffix segment is also closed:
`inverseSquareSingleReverseBefore32_add_32_term_rounds_to_after32` proves the
exact `32^{-2}` step, `inverseSquareSingleReverseAfter32Accumulator_31_to_before16`
proves the compact 15-entry band `31^{-2}, ..., 17^{-2}`,
`inverseSquareSingleReverseBefore16_add_16_term_rounds_to_after16` proves the
`16^{-2}` midpoint/even step, `inverseSquareSingleReverseAfter16Accumulator_15_to_before8`
proves the compact 7-entry band `15^{-2}, ..., 9^{-2}`,
`inverseSquareSingleReverseBefore8_add_8_term_rounds_to_after8` proves the exact
`8^{-2}` step, and `inverseSquareSingleReverseAfter8Accumulator_7_to_before4`
proves the compact 3-entry band `7^{-2}, 6^{-2}, 5^{-2}`.  The theorem
`inverseSquareSingleReverseBefore4SuffixMapsToPrinted_closed` closes the final
explicit additions `4^{-2}, 3^{-2}, 2^{-2}, 1^{-2}`, and
`inverseSquareSingleReverseCandidateSuffixMapsToPrinted_closed` composes the
whole concrete low-index suffix from the named high-prefix candidate to
Higham's printed binary32 reverse accumulator.  The numerical reverse-order
operation-trace gap is now the high-prefix equality or refined tight-window
bridge, not the low-index suffix trace.

## Hidden-Hypothesis Audit

- Relative-error claims still need nonzero exact values when the mathematical
  convention is required; foundational definitions are totalized over `ℝ`.
- Problem 1.1's computed-denominator relative error also requires a nonzero
  computed approximation for the lower comparison; the upper comparison
  theorems assume the corresponding relative error is strictly less than `1`.
- Problem 1.2's theorem is a finite rational ambiguity result for the displayed
  table and its stated one-ulp error bars.  It does not prove an interval
  enclosure for the transcendental value `exp(pi*sqrt(163))`; it proves that
  the table data alone do not imply the pre-decimal units digit is `4`.
- Problem 1.3's square-root rationalization assumes `0 <= x+1`; its quotient
  rewrite for `(1-cos x)/sin x` assumes the source and rewritten denominators
  are nonzero.
- Problem 1.4's complex square-root formulae are exact algebra.  The
  nonnegative-real-part branch assumes `0 <= a` and `a != 0 or b != 0` so
  that `x=sqrt((r+a)/2)` is a valid divisor; the negative-real-part branch
  assumes `a < 0`, which makes `y=sign(b)*sqrt((r-a)/2)` nonzero.  The
  zero input is a separate theorem.  These results do not yet charge the
  floating-point square-root or division calls.
- Problem 1.6's calculator words use an exact digit-to-glyph map and exact
  digit lists.  The `57738.57734 * 10^40` entry is represented by the
  displayed mantissa digits that spell "HELLS BELLS" upside down.  No theorem
  about a specific calculator's display formatting or overflow/range behavior
  is claimed.
- `relError_smul` requires the scale factor to be nonzero.
- Division in `FPModel.model_basicOp` exposes the nonzero denominator condition.
- `compRelError` requires `0 < n` because a maximum over components is nonempty.
- The new mixed forward-backward predicates use absolute perturbation budgets;
  relative or normwise variants must be added for concrete algorithms that use
  those Chapter 1 conventions.
- The new cancellation theorem requires `a - b ≠ 0` for the relative-error
  amplification statement.
- The trigonometric ten-significant-figure example is formalized from the
  displayed decimal approximations as exact rational inputs. The supplied-input
  theorems now prove the scaled direct and rewritten error bounds once cosine
  and sine-half approximation budgets are given, and the finite round-to-even
  wrapper derives those budgets from finite-normal `FloatingPointFormat`
  outputs. They still do not prove that a particular named libm routine or
  decimal-rounding procedure returns the displayed approximations.
- Lemma 1.1 is closed using `opNorm2Le`, the repository's predicate surface for
  operator-2 bounds.  The relative version takes `matrixNormA > 0` as the
  supplied value of `||A||_2`; a future supremum-valued spectral-norm wrapper
  would be packaging, not a paper-level mathematical blocker.
- The Problem 1.9 Cramer condition-number theorems assume the source's
  exact-denominator model, `det(A) != 0`, and `gammaValid fp 3`.  The forward
  relative-error theorem additionally needs `||x||_inf != 0`; the residual
  theorem is scaled by `||b||_inf` and does not need that hypothesis.
- `gepp2_relativeResidual2_le_wilkinson` assumes the local LU solve path
  `fl_forwardSub`/`fl_backSub`, nonzero computed triangular diagonals,
  `gammaValid fp 2`, `gammaValid fp 6`, nonzero computed solution norm,
  `matrixNormA > 0`, the LU backward-error certificate for `gamma fp 2`, and
  the partial-pivoting multiplier bound `|L_hat i j| <= 1`.  Its exact bound
  retains the visible factor `||U_hat||∞ / matrixNormA`; substituting a
  concrete growth-factor or numerical example is a separate instantiation.
- `normwise_forward_from_backward_vec` is deliberately norm-parameterized. It
  assumes `0 < normIn a`, `0 <= κ`, a normwise backward-error witness
  `||Δa||_in <= ε`, and a local condition-number-bound predicate on the same
  radius.  The companion `normwiseConditionNumberSupremumVec` and
  `normwiseConditionNumberAttainedVec` predicates now provide the source-facing
  least-upper-bound and attained-maximum surfaces; compactness/attainment from
  concrete norm/domain hypotheses remains a later specialization.
- `flQuadraticRootPlusFromSqrt_rel_error_le_gamma3` and
  `flQuadraticRootMinusFromSqrt_rel_error_le_gamma3` assume `a != 0` and
  `gammaValid fp 3`. They prove the rounded branch formula after a square-root
  value `s` has been supplied; they do not prove that `s` was computed
  accurately or that the branch is the cancellation-safe choice.
- `quadraticRootSmallByBSign_abs_le_largeByBSign` is exact real algebra: if
  `s >= 0`, choosing the `-` branch for `b >= 0` and the `+` branch for `b < 0`
  gives a branch whose absolute value is at least that of its companion. The
  numerator lemmas also show the opposite branch is small when `s` is close to
  `|b|`. These facts formalize the source's branch-choice/cancellation
  discussion at the exact level.
- `flQuadraticDiscriminant_expansion` exposes the local rounding factors in
  `fl(fl(b*b) - fl(fl(4*a)*c))`; `flQuadraticDiscriminant_abs_error_le` turns
  that trace into a concrete absolute-error radius, and
  `flQuadraticDiscriminant_nonneg_of_abs_error_bound_le` proves conditional
  positivity preservation when that radius is at most the exact discriminant.
  The abstract higher-precision discriminant-evaluation layer is now closed by
  `flQuadraticDiscriminantAbsErrorBound_eq_poly`,
  `flQuadraticDiscriminantAbsErrorBound_le_of_u_le`,
  `flQuadraticDiscriminantAbsErrorBound_le_of_simulatesHigherPrecision`,
  `flQuadraticRootPlusMixedDiscriminantSqrt_abs_error_le`, and
  `flQuadraticRootMinusMixedDiscriminantSqrt_abs_error_le`: a smaller
  discriminant unit roundoff gives a no-larger discriminant error radius, and
  the mixed branch path has an explicit root bound under the discriminant
  separation guard.  These theorems still do not provide an IEEE-double/twice
  round-to-even implementation, exception/overflow semantics, or a general
  range certificate beyond the displayed example.  The small-discriminant case
  where that separation guard fails is handled separately at the exact
  real-root cluster layer by
  `quadraticRootPlus_sub_midpoint_abs_eq`,
  `quadraticRootMinus_sub_midpoint_abs_eq`,
  `quadraticRootSeparation_abs_eq`,
  `quadraticRoots_near_midpoint_of_discriminant_le`, and
  `quadraticRoots_near_midpoint_of_discriminant_guard_failure`.
- `flQuadraticRootPlusWithSqrtRelError_abs_error_le` and
  `flQuadraticRootMinusWithSqrtRelError_abs_error_le` assume `a != 0`,
  `gammaValid fp 3`, `shat=s*(1+epsSqrt)`, and `|epsSqrt| <= fp.u`. They
  charge the supplied relative square-root input error and the subsequent
  rounded branch arithmetic; they do not prove a concrete IEEE square-root
  routine, a branch-safe choice, or overflow/underflow exclusion.
- `flQuadraticRootPlusFromSqrt_abs_input_error_le` and
  `flQuadraticRootMinusFromSqrt_abs_input_error_le` assume `a != 0`,
  `gammaValid fp 3`, `0 <= eta`, and `|shat-s| <= eta`. They charge an
  arbitrary absolute square-root input error and the subsequent rounded branch
  arithmetic; they do not by themselves instantiate `eta` from the rounded
  discriminant trace or a concrete square-root routine.
- `flQuadraticRootPlusFromSqrt_discriminant_abs_error_le` and
  `flQuadraticRootMinusFromSqrt_discriminant_abs_error_le` assume `a != 0`,
  `gammaValid fp 3`, `0 <= quadraticDiscriminant a b c`, `0 <= Dhat`,
  `0 <= etaDisc`, `0 <= etaSqrt`, `|Dhat-quadraticDiscriminant a b c| <=
  etaDisc`, and `|shat-sqrt(Dhat)| <= etaSqrt`. They propagate those
  assumptions to a root bound with input radius `etaSqrt+sqrt etaDisc`; they do
  not by themselves choose a cancellation-safe branch or handle finite-format
  range.
- `flQuadraticRootPlusRoundedDiscriminantSqrt_abs_error_le` and
  `flQuadraticRootMinusRoundedDiscriminantSqrt_abs_error_le` instantiate the
  rounded discriminant, `FPModel.model_sqrt`, and branch arithmetic together.
  They assume `a != 0`, `gammaValid fp 3`, and the separation guard
  `flQuadraticDiscriminantAbsErrorBound fp a b c <= quadraticDiscriminant a b c`;
  the same-precision path uses the same `fp` for discriminant formation,
  square root, and branch arithmetic.  The mixed-precision variants
  `flQuadraticRootPlusMixedDiscriminantSqrt_abs_error_le` and
  `flQuadraticRootMinusMixedDiscriminantSqrt_abs_error_le` instantiate the
  source's higher-precision-discriminant idea at the abstract `FPModel` level.
  Neither path packages a total branch-safe solver for the guard-failure case
  or proves concrete finite-format overflow/underflow exclusions.
- `flQuadraticRootPlusComputedSqrt_abs_error_le` and
  `flQuadraticRootMinusComputedSqrt_abs_error_le` instantiate the relative
  square-root input contract with `FPModel.model_sqrt` applied to the exact real
  discriminant.
  They assume `0 <= quadraticDiscriminant a b c`; they do not charge rounded
  formation of `b^2 - 4*a*c`, branch-safe choice, or finite-format range
  exclusions.
- `flQuadraticRecoveredRootFromOther_abs_error_le_of_abs_error` and the
  `flQuadraticRecoveredRoot*From*` wrappers compose a supplied branch error
  `|xhat-x| <= eta` through the product recovery step when `eta < |x|`. The
  rounded-discriminant endpoint theorems instantiate `xhat` with the computed
  branch and require the named branch radius to be smaller than the exact branch
  root magnitude.
- `flQuadraticRootsByBSignRoundedDiscriminantSqrt_abs_error_le` packages the
  sign-of-`b` rounded pair. It assumes `a != 0`,
  `gammaValid fp 2`, `gammaValid fp 3`, the discriminant separation guard
  `flQuadraticDiscriminantAbsErrorBound fp a b c <= quadraticDiscriminant a b c`,
  a nonzero selected larger exact root, and the selected branch radius smaller
  than that root's magnitude. The guard-failure case is certified at the exact
  root-cluster layer, but this sign-of-`b` rounded-pair theorem does not package
  a total executable fallback branch, nor finite-format overflow/underflow
  exclusions.
- `flQuadraticRecoveredRootFromOther_rel_error_le_gamma2` assumes
  `a*xhat != 0` and `gammaValid fp 2`. It proves the rounding behavior of the
  recovery operation after `xhat` is supplied; it does not prove that `xhat`
  came from a stable square-root/formula path or that overflow/underflow cannot
  occur.
- `quadraticOverflowExample_roots`,
  `quadraticScaledOverflowExample_roots`, and
  `quadraticScaledOverflowExample_variable_scaling` are exact real-arithmetic
  statements about the displayed equations. The companion range theorems
  `quadraticOverflowExample_b_square_single_finiteOverflowRange`,
  `quadraticOverflowExample_b_square_double_finiteNormalRange`,
  `quadraticOverflowExample_four_a_double_finiteNormalRange`,
  `quadraticOverflowExample_four_ac_double_finiteNormalRange`,
  `quadraticOverflowExample_discriminant_double_finiteNormalRange`,
  `quadraticOverflowExample_discriminant_path_double_finiteNormalRange`,
  `quadraticOverflowExample_b_square_double_roundToEvenOp_standardModel`,
  `quadraticOverflowExample_four_a_double_roundToEvenOp_standardModel`,
  `quadraticOverflowExample_four_ac_double_roundToEvenOp_standardModel`,
  `quadraticOverflowExample_discriminant_sub_double_roundToEvenOp_standardModel`,
  `quadraticOverflowExample_exact_discriminant_path_double_ieeeRoundToNearestEvenOpResult_noFlags`,
  `quadraticOverflowExample_discriminant_path_doubleRounded_finiteNormalRange`,
  `quadraticOverflowExample_discriminant_path_doubleRounded_roundToEvenOp_standardModel`,
  `quadraticOverflowExample_discriminant_path_doubleRounded_ieeeRoundToNearestEvenOpResult_noFlags`,
  `quadraticOverflowExample_discriminant_path_doubleRounded_ieeeRoundToNearestEvenOpResult_toReal`,
  `quadraticOverflowExample_scaled_b_square_single_finiteNormalRange`,
  `quadraticOverflowExample_scaled_four_ac_single_finiteNormalRange`, and
  `quadraticOverflowExample_scaled_discriminant_single_finiteNormalRange`
  prove the displayed range facts: unscaled `b*b` overflows single finite
  range, the unscaled `b*b`, `4*a`, `4*a*c`, and exact discriminant are double
  normal finite-range quantities, the exact primitive double operations have
  nearest/even standard-model and no-flag wrappers, the actual rounded
  double trace `fl(fl(b*b)-fl(fl(4*a)*c))` has normal-range, nearest/even
  standard-model, no-flag, and value-field wrappers, and the scaled `b*b`,
  `4*a*c`, and discriminant are single normal finite-range quantities. This
  is still a displayed-example theorem, not a general scaling strategy or a
  complete IEEE special-value semantics.
- The sample-variance one-pass failure example is closed only after exposing
  already-formed aggregates. The zero-output example and negative-output sign
  criterion do not yet prove that single precision rounds the upstream sums to
  `(300060003, 30003)` or to a violating `sumSq < sum^2/n` aggregate pair, nor
  do they prove floating-point stability of the update recurrences. The exact
  update-recursion state and `Q_3/(3-1)=1` result for `[10000,10001,10002]`
  are closed separately.
- Problem 1.7's condition-number theorems assume a positive denominator
  `(n-1)V(x)` where needed.  `sampleVarianceKappaNClosed_eq_expanded` also
  assumes `n != 0` and `n-1 != 0`; `sampleVarianceKappaCClosed_le_KappaNClosed`
  derives the required `n-1 != 0` from the positive denominator.  The
  first-order finite-difference expansion and componentwise/normwise
  directional bounds are closed; `sampleVarianceProblem17RelativeRemainderEnvelope_isBigO`
  now also supplies a literal Landau wrapper for the quadratic relative
  finite-difference remainder.
- Problem 1.8's `mullerExact` theorems are exact real arithmetic for the
  closed-form sequence.  The hidden-mode theorems model a nonnegative
  `100^k` contamination coefficient and prove a qualitative dominance
  mechanism.  The concrete `mullerDecimal4Trace` theorems close a
  four-significant-decimal display-level recurrence trace; they do not derive
  the same behavior from every primitive operation of a named IEEE
  implementation.
- `expOneApproxRoundedBase_eq_exact_base_mul_initial_error_pow` models only
  the initial rounded formation of `1 + 1/n` followed by exact exponentiation.
  `expOneApproxRoundedBase_relError_eq_initial_error_pow_abs` adds the exact
  relative-error formula `|(1+delta)^n - 1|` under the same model.
  It does not charge the exponentiation routine's own floating-point operations
  or derive the Table 1.1 values from a concrete Fortran execution trace.
  The displayed Table 1.1 finite data itself is now encoded and checked by the
  `expOneApproxTable11_*_rows` theorems.
- Problem 1.5's log-exp result treats the supplied logarithm and final
  exponential as carrying visible relative errors `epsLog` and `epsExp`.
  The composition theorem proves the relative-error bound
  `exp(u)*(1+u)-1` when both errors are bounded by `u`; the finite
  round-to-even wrapper now derives those two errors from finite-normal
  `FloatingPointFormat.finiteRoundToEven` outputs. A full named libm/IEEE or
  Fortran implementation proof remains open.
- `noPivotRoundedLU_error_matrix` assumes the rounded update has already
  produced `fl(1+epsilon^{-1}) = epsilon^{-1}` and assumes `epsilon != 0`.
  It proves the displayed factor-reproduction failure from that modeled
  rounded value. The concrete IEEE-single instance `epsilon=2^{-24}` is
  closed by `noPivotIeeeSingle_add_one_inv_epsilon_rounds_to_inv`, and
  `noPivotIeeeSingleSmallEpsilon_error_matrix` specializes the reproduction
  failure to that epsilon. The representable-inverse binade criterion is now
  closed by `noPivotIeeeSingle_add_one_normalized_rounds_to_self_of_two_lt_ulp`;
  `noPivotIeeeSingle_add_one_normalized_rounds_to_self_of_exp_ge_26` and
  `noPivotIeeeSingle_add_one_inv_rounds_to_inv_of_inv_normalized_exp_ge_26`
  specialize it to every positive IEEE-single representable inverse with
  exponent at least `26`. The ulp-`2` exponent-25 boundary is now classified by
  `noPivotIeeeSingle_add_one_normalized_rounds_to_self_of_ulp_eq_two_even`,
  `noPivotIeeeSingle_add_one_normalized_rounds_to_succ_of_ulp_eq_two_odd`,
  the exponent-25 even/odd wrappers, and
  `noPivotIeeeSingle_add_one_normalized_exp25_max_rounds_to_exp26_min` for the
  carry endpoint. The left-rounding cases are packaged by
  `noPivotIeeeSingle_add_one_inv_rounds_to_inv_of_inv_normalized_left_rounding_cases`.
  The source-facing real-`epsilon` representability guard is closed by
  `noPivotIeeeSingle_add_one_inv_rounds_to_inv_requires_inv_finiteSystem` and
  `noPivotIeeeSingle_add_one_inv_not_rounds_to_inv_of_inv_not_finiteSystem`.
- `noPivotPartialPivotLUFactSpec` proves the exact row-swap `P*A=L*U`
  branch for the same §1.12.1 matrix, with
  `noPivotPartialPivotLUBackwardError_zero` giving the zero-perturbation
  pivoted LU backward-error certificate and
  `noPivotPartialPivot_multiplier_abs_le_one` closing the source-regime
  multiplier bound. The concrete IEEE-single primitive pivoted path at
  `epsilon=2^{-24}` is closed by
  `noPivotIeeeSingle_partialPivot_div_epsilon_one_rounds_to_epsilon`,
  `noPivotIeeeSingle_partialPivot_mul_epsilon_one_rounds_to_epsilon`,
  `noPivotIeeeSingle_add_one_epsilon_rounds_to_one`,
  `noPivotIeeeSingle_partialPivot_sub_neg_one_epsilon_rounds_to_neg_one`,
  and `noPivotIeeeSinglePartialPivotRoundedLUBackwardError`. The finite
  all-small pivoted primitive layer is closed by
  `noPivotIeeeSingle_partialPivot_div_epsilon_one_rounds_to_epsilon_of_finiteSystem`,
  `noPivotIeeeSingle_partialPivot_mul_epsilon_one_rounds_to_epsilon_of_finiteSystem`,
  `noPivotIeeeSingle_add_one_epsilon_rounds_to_one_of_nonneg_le_small`, and
  `noPivotIeeeSingle_partialPivot_sub_neg_one_epsilon_rounds_to_neg_one_of_nonneg_le_small`.
  The generic
  supplied-operation bridge is closed by
  `noPivotPartialPivotPrimitiveRoundedU_eq_roundedU_of_rounds`,
  `noPivotPartialPivotRoundedLUBackwardError`, and
  `noPivotPartialPivotPrimitiveRoundedLUBackwardError_of_rounds`: supplied
  facts `fl(epsilon/1)=epsilon`, `fl(epsilon*1)=epsilon`, and
  `fl((-1)-epsilon)=-1` imply the rounded pivoted factors satisfy the
  componentwise pivoted LU backward-error certificate with radius `epsilon`.
  The no-pivot real-`epsilon` representability guard in this §1.12.1 branch is
  closed by the finite-output guard theorems.
- `noPivotExample_kappaInf_eq` assumes `0 < epsilon <= 1` and uses the
  displayed exact inverse `noPivotExampleAInv`; the two-sided inverse property
  is separately closed by `noPivotExampleAInv_isInverse`.
- `repeatedSquare_repeatedSqrt_sixty_eq_self` is an exact real-arithmetic
  baseline. It does not model HP 48G decimal precision, the representable
  range, rounding to `1.0`, underflow to zero, or overflow behavior.
- `hp48gSqrtSquareSurrogate_relError_100` and the interval theorems
  `hp48gSqrtSquareSurrogate_absError_of_ge_one`,
  `hp48gSqrtSquareSurrogate_relError_of_ge_one`,
  `hp48gSqrtSquareSurrogate_absError_of_nonneg_lt_one`, and
  `hp48gSqrtSquareSurrogate_relError_of_pos_lt_one` prove the relative error
  at `x=100` and the displayed surrogate's source-interval error formulas.
  The theorem `hp48gSqrtSquareTrace_eq_surrogate_of_laws` now derives that
  surrogate from the compact `Hp48gSqrtSquareSurrogateLaws` phase interface.
  It still does not instantiate those phase laws from an HP 48G machine model,
  decimal precision, exponent range, rounding-to-one, or underflow-to-zero
  semantics.
- `inverseSquareTerm_le_two_pow_neg_24_of_ge` is an exact real-arithmetic
  term-size/tail bound, with positivity supplied by `inverseSquareTerm_pos_of_pos`.
  `inverseSquareTerm_between_half_ulp_and_one_ulp_of_ge_2897_lt_4096` proves the
  strict pre-plateau interval `2^-24 < 1/k^2 < 2^-23` for every
  `2897 <= k < 4096`, so this part of the summation argument is now a range
  theorem rather than an endpoint enumeration.
  `inverseSquareSingle_add_term_rounds_to_next_of_half_ulp_lt` proves the
  reusable local binary32 successor rule: if the inverse-square term is between
  one half-ulp and one ulp at exponent `1`, adding it to a normal positive
  mantissa with adjacent successor rounds to that successor by a strict
  right-closer comparison, under explicit finite-range hypotheses.
  `inverseSquareSingle_add_term_rounds_to_next_of_index_range` composes that
  successor rule with the `2897 <= k < 4096` term-size interval.
  `inverseSquareSingleEarlyMantissaPrefix_2895_eq` and
  `inverseSquareSingleEarlyMantissaPrefix_2895_add_base_eq_preWindow` certify
  the integer mantissa-increment sum for terms `2, ..., 2896`; this is a
  checked arithmetic certificate, not a hand enumeration of the early prefix.
  `inverseSquareSingleEarlyMantissaIncrementNearestCertificateBool_eq_true`
  proves the bounded Boolean certificate, and
  `inverseSquareSingleEarlyMantissaIncrementNearestCertificate` extracts, for
  each early term, the strict half-ulp nearest-increment inequalities and the
  mantissa-range bound needed by the finite-format source-rounding bridge.
  `inverseSquareSingleForwardAccumulator_one_eq_one` closes the actual first
  rounded-addition step, and
  `inverseSquareSingleForwardAccumulator_2896_eq_prePlateauWindowStart_of_early_mantissa_increment_rule`
  reduces the actual early prefix through `k = 2896` to the uniform local rule
  `inverseSquareSingleEarlyMantissaIncrementRule`.
  `inverseSquareSingle_add_term_rounds_to_nearest_mantissa_of_scaled_bounds`
  bridges the scaled nearest-increment inequalities to the source-rounded
  binary32 selector, `inverseSquareSingleEarlyMantissaIncrementRule_closed`
  closes the uniform local early-increment rule, and
  `inverseSquareSingleForwardAccumulator_2896_eq_prePlateauWindowStart`
  removes the early-prefix assumption for the actual accumulator.
  `inverseSquareSingleForwardAccumulatorFrom_normalizedValue_of_index_window`
  lifts that per-step result to a recursive accumulator over an arbitrary
  finite index window with visible normalized-mantissa and index-range
  hypotheses, and
  `inverseSquareSingleForwardAccumulatorFrom_prePlateauWindowStart_2897_of_le_1194`
  proves every intermediate prefix value in the 2897--4090 window.
  `inverseSquareSingleForwardAccumulatorFrom_prePlateauWindowStart_2897_1194_eq_sixBeforePlateau`
  instantiates that induction for the whole `k = 2897, ..., 4090` window from
  the pre-window accumulator to the six-before-plateau accumulator.
  `inverseSquareSingleForwardAccumulatorFrom_prePlateauWindowStart_2897_1200_add_eq_plateau`
  composes that window with the tail theorem, while
  `inverseSquareSingleForwardAccumulatorFrom_sixBeforePlateau_4091_six_add_eq_plateau`
  proves the whole `k >= 4091` tail once the six-before-plateau accumulator has
  been reached.
  `inverseSquareSingleForwardAccumulatorFrom_sixBeforePlateau_4091_of_le_5`
  and
  `inverseSquareSingleForwardAccumulatorFrom_prePlateauWindowStart_2897_lt_plateau_of_lt_1200`
  additionally prove that the already-closed `k = 2897, ..., 4095` segment has
  not yet reached the plateau, and
  `inverseSquareSingleForwardAccumulator_4096_add_eq_plateau_of_early_mantissa_increment_rule`
  plus
  `inverseSquareSingleForwardAccumulator_2896_add_lt_plateau_of_early_mantissa_increment_rule`
  connect these facts to the actual accumulator from zero under that uniform
  local early-increment rule.  The older wrappers
  `inverseSquareSingleForwardAccumulator_4096_add_eq_plateau_of_2896_eq_prePlateauWindowStart`
  plus
  `inverseSquareSingleForwardAccumulator_2896_add_lt_plateau_of_2896_eq_prePlateauWindowStart`
  remain available if the pre-window accumulator equality is supplied directly.
  `inverseSquareSingleSixBeforePlateau_add_4091_term_rounds_to_fiveBeforePlateau`
  proves the strict-right-closer step from the six-before-plateau binary32
  accumulator to the five-before-plateau binary32 accumulator at `k = 4091`.
  `inverseSquareSingleFiveBeforePlateau_add_4092_term_rounds_to_fourBeforePlateau`
  proves the strict-right-closer step from the five-before-plateau binary32
  accumulator to the four-before-plateau binary32 accumulator at `k = 4092`.
  `inverseSquareSingleFourBeforePlateau_add_4093_term_rounds_to_threeBeforePlateau`
  proves the strict-right-closer step from the four-before-plateau binary32
  accumulator to the three-before-plateau binary32 accumulator at `k = 4093`.
  `inverseSquareSingleThreeBeforePlateau_add_4094_term_rounds_to_twoBeforePlateau`
  proves the strict-right-closer step from the three-before-plateau binary32
  accumulator to the two-before-plateau binary32 accumulator at `k = 4094`.
  `inverseSquareSingleTwoBeforePlateau_add_4095_term_rounds_to_prePlateau`
  proves the strict-right-closer step from the two-before-plateau binary32
  accumulator to the immediately preceding binary32 accumulator at `k = 4095`.
  `inverseSquareSinglePrePlateau_add_4096_term_rounds_to_plateau` proves the
  local odd-left-mantissa midpoint step from the immediately preceding binary32
  accumulator into the plateau. `inverseSquareSinglePlateau_add_4096_term_rounds_to_self`
  proves the local binary32 nearest/even midpoint drop-off at the concrete
  even-mantissa accumulator printed approximately as `1.64472532`, and
  `inverseSquareSinglePlateau_add_term_rounds_to_self_of_ge_4096` proves every
  later `1/k^2` term rounds away once that plateau value has been reached.
  Finally,
  `inverseSquareSingleForwardAccumulator_2896_add_lt_plateau` and
  `inverseSquareSingleForwardAccumulator_4096_add_eq_plateau` remove the
  early-rule assumption and prove the fully unconditional left-to-right
  first-stagnation trace for the modeled binary32 loop.  The reverse-order
  loop shape and `10^9`/`4096` split are now named by
  `inverseSquareSingleReverseAccumulatorFrom`,
  `inverseSquareSingleReverseAccumulator`, and
  `inverseSquareSingleReverseAccumulator_ten_pow_nine_split_4096`; the
  high-prefix index and term-size bounds are named by
  `inverseSquareReverseTenPowNineHighPrefix_index_ge_4097` and
  `inverseSquareTerm_le_two_pow_neg_24_of_reverse_ten_pow_nine_high_prefix`.
  The exact reverse split and high-index mass are bounded non-enumeratively by
  `inverseSquareExactReverseAccumulatorFrom_add`,
  `inverseSquareExactReverseAccumulator_ten_pow_nine_split_4096`,
  `inverseSquareExactReverseAccumulator_ten_pow_nine_eq_highPrefix_add_low4096`,
  `inverseSquareTerm_le_telescope`,
  `inverseSquareExactReverseAccumulatorFrom_le_telescope`, and
  `inverseSquareExactReverseTenPowNineHighPrefix_le_inv_4096`, with
  `inverseSquareExactReverseAccumulator_ten_pow_nine_sub_low4096_le_inv_4096`
  giving the exact excess-over-low-tail bound.  The matching lower telescope
  is named by `inverseSquareTerm_ge_telescope_succ` and
  `inverseSquareExactReverseAccumulatorFrom_ge_telescope_succ`; the concrete
  suffix-start squeeze is packaged by
  `inverseSquareExactReverseTenPowNineHighPrefix_mem_printedSuffixStartWindow`
  and the tighter
  `inverseSquareExactReverseTenPowNineHighPrefix_mem_printedSuffixStartTightWindow`
  and
  `inverseSquareExactReverseAccumulator_ten_pow_nine_sub_low4096_mem_printedSuffixStartWindow`.
  The broad rounded final-value reduction is named by
  `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_window_certificates`,
  and the refined viable reduction is named by
  `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_tight_window_certificates`,
  leaving the rounded high-prefix tight-window certificate
  `inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow` and
  the suffix certificate `inverseSquareSingleReverseTightSuffixWindowMapsToPrinted`
  before the printed value can be closed by the window route.
  The concrete candidate path further reduces this to proving
  `inverseSquareSingleReverseTenPowNineHighPrefixEqCandidate` and
  `inverseSquareSingleReverseCandidateSuffixMapsToPrinted`; the candidate is
  already proved to lie in the suffix-start window. The reusable local
  certificate bridges
  `inverseSquareSingleForwardStep_eq_left_of_adjacent_strict_between_left_closer`
  and
  `inverseSquareSingleForwardStep_eq_right_of_adjacent_strict_between_right_closer`
  now expose the compact adjacent-bracket proof shape for suffix chunks. The exact first
  suffix step `4096^{-2}` is closed by
  `inverseSquareSingleReverseCandidate_add_4096_term_rounds_to_after4096`,
  and the second suffix step `4095^{-2}` is closed by
  `inverseSquareSingleReverseAfter4096_add_4095_term_rounds_to_after4095`,
  reducing the concrete suffix trace to the intended compact certificate
  `inverseSquareSingleReverseAfter4095SuffixMapsToPrinted`.
  The remaining §1.12.3 gap is the reported reverse-order `10^9`-term
  summation value and related summation-order examples.
- `increasingPrecisionSinExampleSource_perturbation_abs_le` proves the exact
  source-function perturbation bound
  `|x + 10^{-8} sin(2^{24}x) - x| <= 10^{-8}`, and
  `increasingPrecisionSinExampleSource_finiteRoundToEven_eq_base_of_spacing`
  proves the finite-format plateau once `x` is separated by more than
  `2*10^{-8}` from every other finite-format value.
  `increasingPrecisionSinExampleSource_ieeeSingle_roundToEven_one`
  instantiates this at binary32 base point `x = 1`.  The remaining sine-plateau
  gap is the rest of the displayed interval `22 < t < 31`, the displayed
  `-8.55e-9` numerical sine value, and the concrete rounded `x = 1/7`
  sine-expression plateau/error trace beyond the already closed input-storage
  values and exact representation errors.  The early-grid representation
  dominance is closed separately by
  `increasingPrecision_one_seventh_binary_grid_abs_error_ge` and
  `increasingPrecision_one_seventh_binary_grid_abs_error_gt_scale_of_t_le_twenty`:
  every dyadic `z/2^t` is at least `1/(7*2^t)` away from `1/7`, and for
  `t <= 20` this is already larger than the source amplitude `10^-8`.
- `increasingPrecisionExampleElse_relError_one_of_expHat_one` assumes the
  computation has entered the else branch with nonzero `y` and that the
  exponential evaluation supplied to the branch has rounded to `1`.
  `increasingPrecisionExampleElse_two_precision_failure_of_expHat_one`
  extends this to two supplied precision runs, proving both return `0` and
  both have relative error `1` against `f(2/3) = 1`. These theorems do not
  derive those supplied facts from single- or double-precision Fortran
  arithmetic.
- `two_thirds_not_binaryTerminating`, `one_seventh_not_binaryTerminating`,
  `two_thirds_not_ieeeSingleFiniteSystem`, `two_thirds_not_ieeeDoubleFiniteSystem`,
  `one_seventh_not_ieeeSingleFiniteSystem`, and
  `one_seventh_not_ieeeDoubleFiniteSystem` close the finite-storage exactness
  obstruction for the §1.13 source inputs `2/3` and `1/7`: neither IEEE single
  nor IEEE double can store either exact rational as a finite value.  The
  source-shaped wrapper
  `increasingPrecisionExampleElse_two_precision_failure_of_ieee_roundToEven_stored_source_expHat_one`
  therefore applies the supplied-`exp(y)=1` two-run failure theorem to the
  single and double finite round-to-even stored source inputs.  This still does
  not derive the hidden Fortran/libm `exp(y)` rounding trace.
  `increasingPrecision_ieeeSingle_roundToEven_one_seventh` and
  `increasingPrecision_ieeeDouble_roundToEven_one_seventh` identify the
  concrete finite round-to-even stored source values for the sine example's
  `x = 1/7` as `9586981*2^-26` and `5146971002709138*2^-55`, while
  `increasingPrecision_ieeeSingle_roundToEven_one_seventh_error` and
  `increasingPrecision_ieeeDouble_roundToEven_one_seventh_error` prove their
  exact representation errors are `3/(7*2^26)` and `-2/(7*2^55)`.
- `increasingPrecision_ieeeSingle_roundToEven_two_thirds` and
  `increasingPrecision_ieeeDouble_roundToEven_two_thirds` identify the concrete
  round-to-even stored values of source input `2/3` as `11184811*2^-24` and
  `6004799503160661*2^-53`.  The branch-variable theorems reduce these to
  `2^-24/25` and `2^-53/25`, and
  `increasingPrecision_ieeeSingle_roundToEven_exp_branch_y_eq_one` plus
  `increasingPrecision_ieeeDouble_roundToEven_exp_branch_y_eq_one` prove that
  correctly rounded finite-format exponentials of those tiny values are both
  `1`.  The wrapper
  `increasingPrecisionExampleElse_two_precision_failure_of_ieee_roundToEven_stored_exp_source`
  therefore closes the no-supplied-exp version of the modeled single/double
  branch failure.  This is a repository-model finite round-to-even trace, not a
  certificate for an unspecified vendor `exp` routine.
- `expm1Algorithm2Exact_eq_algorithm1Exact` is exact real arithmetic. It uses
  `Real.log_exp` and `Real.exp_eq_one_iff`; it does not model rounded exp/log,
  guard-digit subtraction, or the final `3.5u` bound.
- `expm1Table12_x_rows`, `expm1Table12_algorithm1_rows`, and
  `expm1Table12_algorithm2_rows` are exact finite-data transcriptions of the
  displayed Table 1.2 decimals, while
  `expm1Table12_algorithm2_ten_pow_neg15_last_digit_correction` formalizes the
  source's last-digit correction note for the `10^-15` Algorithm 2 row. These
  theorems do not derive the table entries from MATLAB, IEEE arithmetic, or
  concrete libm `exp`/`log` implementations.
- `expm1Page23_displayed_single_precision_ratio` and
  `expm1Page23_displayed_exact_arithmetic_ratio` reduce the two page-23
  displayed decimal ratio lines to exact rational ratios when the displayed
  significands are read literally. They do not model the `fl` operator or the
  single-precision rounding path that produced the displayed quantities.
- `expm1LogRatio_tendsto_one` is exact real analysis for the punctured-neighborhood
  limit of `g(y)=(y-1)/log(y)` at `y=1`. It does not prove quantitative
  slow-variation estimates, derivative bounds over a finite interval, rounded
  exp/log contracts, or the final `3.5u` bound.
- `expm1Log_one_add_sub_linear_quadratic_abs_le`,
  `expm1LogRatioDenRemainder_abs_le`, and
  `expm1LogRatio_one_add_eq_inv_one_sub_half_add_remainder` are exact
  real/complex-analysis consequences of the Taylor bound for `log(1+v)` under
  `|v| < 1` and, for the reciprocal rewrite, `v != 0`. They close the
  denominator `O(v^2)` expansion used on page 24, but they do not yet compare
  `g(yhat)` with `g(y)`, instantiate rounded exp/log routines, or prove the
  final `3.5u` relative-error theorem.
- `expm1LogRatio_one_add_sub_one_add_half_abs_le` is an exact real-analysis
  quantitative `O(v^2)` statement for the printed expansion
  `g(1+v)=1+v/2+O(v^2)` on `|v| <= 1/2`, `v != 0`.
- `expm1LogRatio_one_add_diff_sub_half_abs_le` is the exact real-analysis
  two-point comparison behind `g(yhat)-g(y) ≈ (yhat-y)/2` after writing
  `yhat=1+w`, `y=1+v`.
- `expm1LogRatio_mul_one_add_delta_diff_sub_y_delta_half_abs_le` and
  `expm1LogRatio_mul_one_add_delta_diff_sub_delta_half_abs_le` substitute
  `yhat=y*(1+delta)` into that exact-analysis comparison. They close the
  `yhat-y = y*delta` and `y ≈ 1` steps with explicit remainder terms.
- `expm1LogRatio_sub_one_abs_le`, `expm1LogRatio_self_sub_abs_le`, and
  `expm1LogRatio_mul_one_add_delta_diff_sub_logRatio_delta_half_abs_le` close
  the remaining exact `delta` to `g(y)*delta` substitution layer. They still
  do not instantiate exp/log floating-point contracts.
- `expm1LogRatio_abs_ge_one_sub_radius_bound` and
  `expm1LogRatio_abs_ge_half_of_radius` close the corresponding local
  denominator lower-bound bridge for `|g(y)|`; they do not by themselves bound
  the rounded exponential/logarithm inputs.
- `expm1Algorithm2RoundedCore_eq_source_1_9` assumes the rounded logarithm has
  already been supplied as `logHat = log(yhat)*(1+epsLog)` with
  `|epsLog| <= u`, and it uses the local `FPModel.model_sub` and
  `FPModel.model_div` laws for subtraction and division. It does not prove a
  concrete exp/log implementation contract, nor the subsequent slow-variation
  estimates that turn (1.9) into the roughly `3.5u` bound; the later
  finite-normal rounded-log adapter discharges the rounded-log witness only on
  the finite round-to-even normal-range route.
- `expm1Algorithm2RoundedCore_eq_source_1_9_of_exact_sub`,
  `expm1Algorithm2RoundedCore_eq_source_1_9_of_guardDigitSubtractionModel`,
  and
  `expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_ferguson`
  close the exact-subtraction branch of equation (1.9): if the local
  subtraction is exact, or if a guard-digit/Ferguson finite-format hypothesis
  proves it exact, then Lean takes `epsSub = 0`. These are conditional
  alternate instantiations; the preferred small-`x` machine path now uses the
  Sterbenz-radius route below rather than proving Ferguson cases for the actual
  produced `yhat`.
- `expm1Algorithm2_yhat_one_sterbenzRatioCondition_of_abs_sub_one_le_third`
  and
  `expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_sterbenz_radius`
  provide the better local small-`x` exact-subtraction route: the same
  `|yhat-1| <= 1/3` radius used in the `3.5u` proof implies Sterbenz's ratio
  condition, so finite round-to-even subtraction is exact once `yhat` and `1`
  are finite representable and the concrete subtraction operation is linked to
  `finiteRoundToEvenOp`. The wrappers
  `expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_exp_perturb_sterbenz_radius`,
  `expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_exp_x_sterbenz_radius`,
  and
  `expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_exp_x_mul_one_add_u_sterbenz`
  derive that radius directly from the rounded-exponential hypotheses.
- `expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_exact_sub` and
  `expm1Algorithm2RoundedCore_relError_le_gamma2_of_exact_sub` sharpen the
  exact-subtraction branch: once `fp.fl_sub yhat 1 = yhat - 1`, only the
  rounded logarithm and final division factors are charged, giving a `gamma_2`
  core around `g(yhat)`. The source-domain finite round-to-even/Sterbenz
  wrappers with suffix `_exp_x_mul_one_add_u_sterbenz` derive the same
  `gamma_2` core from the compact smallness condition `exp X*(1+u) <= 4/3`.
  The rounded-exp-produced variants discharge the `yhat` finite hypothesis from
  `yhat = finiteRoundToEven(exp x)` using the finite-output lemma for
  `finiteRoundToEven`; the finite-normal exp/log variants additionally derive
  the rounded-exp `delta` and rounded-log `epsLog` witnesses from the
  corresponding finite round-to-even normal-range contracts. They still require
  the concrete subtraction operation link to `finiteRoundToEvenOp`.
- `expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma4` additionally assumes
  `0 < 1+epsLog` and `gammaValid fp 4`. It is a generic gamma-calculus
  wrapper around `g(yhat)`, not the source's sharper small-`x` estimate that
  leads to a roughly `3.5u` bound.
- `expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma3` and
  `expm1Algorithm2RoundedCore_relError_le_gamma3` are the sharper signed-product
  version of the same local arithmetic step. They account for the three
  equation (1.9) factors as `gamma_3`, but still assume the rounded logarithm
  and rounded subtraction model inputs rather than deriving the full concrete
  machine exp/log path and operation links. On the finite-normal rounded-exp/log
  Sterbenz route, `yhat` finite representability, the rounded-exp
  `|delta| <= fp.u` hypothesis, and the rounded-log `epsLog` witness are
  discharged by the dedicated adapters above.
- `expm1Algorithm2RoundedCore_relError_le_gamma4` and
  `expm1Algorithm2RoundedCore_relError_le_local_bound` turn the gamma wrapper
  into Chapter 1 relative-error statements, including a local budget back to
  `g(y)` under `yhat=y*(1+delta)`. They still rely on supplied exp/log
  contracts and do not instantiate the final roughly `3.5u` machine theorem.
- `expm1Algorithm2RoundedCore_relError_le_local_bound_gamma3`,
  `expm1Algorithm2RoundedCore_relError_le_eta_add_gamma3`, and
  `expm1Algorithm2RoundedCore_relError_le_eta_add_gamma3_of_primitive_bounds`
  carry the sharper arithmetic factor through the same local drift certificate,
  producing `eta + (1+eta)*gamma_3`. They are the correct first-order route to
  `0.5u+3u`. The corollaries
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_remainder`
  and
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_remainder_of_primitive_bounds`
  now state the explicit higher-order `3.5u`-style bound, but they still rely on
  a drift hypothesis that must be proved from concrete exp/log contracts and
  operation-link assumptions; on the finite-normal rounded-exp route, `yhat`
  finite representability and `|delta| <= fp.u` are supplied by the dedicated
  adapters.
- `expm1Algorithm2PrimitiveSlowRemainderBound`,
  `expm1Algorithm2PrimitiveDriftBound_le_half_u_mul_abs_logRatio_add_slow_remainder`,
  and
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_local_remainder_of_abs_bounds`
  remove that all-or-nothing drift hypothesis from the first-order route: the
  leading `(u/2)*|g(y)|` term follows from `deltaAbs <= u`, and the remaining
  obligation is the explicit slow-ratio remainder normalized by `|g(y)|`.
- `expm1Algorithm2PrimitiveSlowRemainderBound_le_of_radius` and
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_radius_remainder_of_abs_bounds`
  compress that explicit remainder to a single local-radius expression when
  both `yAbs` and `yhatAbs` are at most `r`. This is a reusable interval bridge,
  not a concrete exp/log or machine-specific proof.
- `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_radius_bound_of_abs_bounds`
  combines the radius remainder with the local denominator bound `1/2 <= |g(y)|`
  under `r <= 1/3`, removing the explicit division by `|g(y)|`. This still
  awaits concrete exp/log and actual-`yhat` finite-format hypotheses that prove
  the radius assumptions for an implementation path.
- `expm1Algorithm2_yhat_sub_one_abs_le_of_y_radius` and
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_perturb_radius_bound`
  close the source-shaped rounded-exponential radius handoff: if
  `|y-1| <= r` and `|delta| <= u`, then
  `|y*(1+delta)-1| <= r + (1+r)u`, and the `3.5u` theorem can use that
  combined radius directly. This is not a concrete small-`x` theorem yet; it
  still awaits an implementation/source-domain proof that `y=e^x` is close
  enough to `1` and that `r + (1+r)u <= 1/3`.
- `expm1Algorithm2_exp_sub_one_abs_le_of_abs_x_le`,
  `expm1LogRatio_exp_ne_zero_of_ne_zero`, and
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_x_radius_bound`
  close the next small-`x` adapter: `|x| <= X` gives
  `|exp x - 1| <= exp X - 1`, and the local theorem uses the radius
  `(exp X - 1) + exp X*u`.
- `expm1Algorithm2_exp_x_combined_radius_le_third_of_exp_mul_one_add_u_le`
  and
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_x_mul_one_add_u_bound`
  close the abstract scalar smallness side condition by replacing
  `(exp X - 1) + exp X*u <= 1/3` with the compact source-domain hypothesis
  `exp X*(1+u) <= 4/3`. The remaining implementation-facing obligations are
  concrete exp/log routine contracts, Ferguson-condition verification for the
  actual rounded `yhat`, and Table 1.2 machine derivation.
- `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_u_radius_bound_of_abs_bounds`
  specializes the radius assumptions to `yAbs <= u` and `yhatAbs <= u`,
  leaving the explicit higher-order tail
  `((25/2)*u^2 + 3*u^3)*(1+gamma_3)`. This is still a local bridge, not a
  concrete exp/log routine instantiation.
- `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_u_radius_bound_of_unit_bounds`
  is the direct local theorem closest to the page-24 use case: it consumes
  `|y-1| <= u`, `|yhat-1| <= u`, and `|delta| <= u` directly and avoids
  enumerating auxiliary radius cases. This still awaits the concrete exp/log
  and actual-`yhat` finite-format hypotheses that prove those three unit bounds
  for an implementation path.
- `expm1Algorithm2ThreePointFiveUnitBound`,
  `expm1Algorithm2Gamma3Scalar`,
  `expm1Algorithm2ThreePointFiveUnitBoundScalar`,
  `expm1Algorithm2ThreePointFiveUnitBound_eq_scalar`,
  `expm1Algorithm2ThreePointFiveUnitBoundScalar_isBigO`,
  `expm1Algorithm2ThreePointFiveUnitBound_eq_zero_of_u_eq_zero`, and
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_unit_bound_of_unit_bounds`
  package that detailed unit-bound RHS behind one named local bound, expose the
  same expression as a scalar envelope in `u`, prove the scalar envelope is
  `O(u)` as `u -> 0`, and prove it is non-vacuous in the zero-roundoff sanity
  case.
- `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_normalized_remainder_of_abs_bounds`
  is the final local wrapper on this branch: it consumes the single certificate
  `S <= rem*|g(y)|` for the explicit slow-ratio remainder and adds only
  `rem*(1+gamma_3)` to the leading `3.5u` theorem.
- `expm1Algorithm2LocalRelErrorBound_le_eta_add_gamma4` and
  `expm1Algorithm2RoundedCore_relError_le_eta_add_gamma4` are certificate
  consumers: a future drift proof `drift <= eta*|g(y)|` immediately yields the
  source-shaped bound `eta + (1+eta)*gamma_4`. They do not themselves prove the
  exp/log drift certificate.
- `expm1Algorithm2PrimitiveDriftBound`,
  `expm1Algorithm2SlowRatioPerturbationBound_le_of_abs_bounds`,
  `expm1Algorithm2LocalDrift_le_primitive_bound`, and
  `expm1Algorithm2RoundedCore_relError_le_eta_add_gamma4_of_primitive_bounds`
  are the next compact bridge: they turn elementary absolute-value estimates
  into that normalized drift certificate, but still require a concrete
  exp/log/machine instantiation plus subtraction operation-link
  verification before the source's roughly `3.5u` statement is closed.
- `givensRotation_trig_orthogonal` assumes the two embedded coordinates are
  distinct. It is exact orthogonality of the source's displayed trigonometric
  block, not a floating-point QR theorem and not an instantiation of the
  worked numerical matrices in §1.14.2.
- `givensRotation_mulVec_p`, `givensRotation_mulVec_q`,
  `givensRotation_ratio_zeroes_q`, and `givensRotation_ratio_mulVec_p` are exact
  real-arithmetic two-entry Givens action and zeroing facts. They do not prove
  a floating-point Givens kernel or instantiate the hidden numerical QR example.
- `beneficialPowerCharDet_eq` and the associated root/display-accuracy theorems
  are exact characteristic-determinant algebra for the displayed rational
  matrix entries. They do not prove spectral perturbation bounds for `A+DeltaA`.
- `beneficialPowerFirstStep_zero` is exact real arithmetic for the unnormalized
  first power-method multiplication. `beneficialPowerFirstStep_perturbed_eq_delta`
  models only the exact effect of supplying a perturbed stored matrix
  `A+DeltaA`: the first step equals `DeltaA*[1,1,1]^T`. These perturbation
  theorems do not by themselves derive the actual rounded entries or concrete
  perturbation size of the displayed decimal matrix; that entrywise
  IEEE-double storage vector and its `10^-16` scale are now closed separately
  by `beneficialPowerMatrixIeeeDoubleRounded_firstStep_eq` and
  `beneficialPowerMatrixIeeeDoubleRounded_firstStep_abs_between_one_e17_one_e16`.
  They still do not derive the subsequent infinity-norm scaling after the exact
  zero vector, a hidden MATLAB primitive-operation/BLAS matrix-vector
  multiplication trace, or convergence of the perturbed problem.
  `beneficialPowerFirstStep_perturbed_vecNorm2_pos_of_delta_row_sum_ne_zero`
  only lifts this supplied perturbation model to a positive-norm conclusion; it
  does not identify the actual IEEE perturbation.
- `inverseIteration_shiftedSystem_solution_on_eigenvector` and
  `inverseIteration_shiftedInverse_mul_eigenvector_of_leftInverse` are exact
  shifted-system facts: on an eigenvector right-hand side, `(A-mu I)y=x` has
  the solution `y=(lambda-mu)^{-1}x`, and any left inverse of `A-mu I` acts
  that way. `inverseIteration_shiftedInverse_amplification_strict_of_abs_shift_lt`
  closes only the scalar amplification relation as `mu` moves closer to an
  eigenvalue. `inverseIteration_parallel_error_output_isRightEigenpair` closes
  the exact harmlessness implication once an error parallel to the eigenvector
  is supplied. These do not prove the cited Parlett/Golub--Van Loan perturbation
  theorem that the floating-point solve error is actually almost entirely in the
  required eigenvector direction.
- `hessenbergDiagRoundedStep_eq_perturbed_exactStep` is scalar algebra for one
  displayed §1.16 diagonal update. `hessenbergEntrywisePerturbation` and
  `hessenbergDiagRoundedStep_eq_entrywisePerturbedExactStep` now construct the
  entrywise nearby matrix used by that update formula, and
  `hessenbergRoundedDiagTraceOnOriginal_exactTraceOnEntrywisePerturbation`
  packages all updated diagonal entries against that one global nearby matrix,
  and `hessenbergRoundedDiagTraceOnOriginal_nearbyDet_relError_le_gamma`
  combines that trace with a supplied nearby-matrix determinant-product
  certificate to get the final `gamma_n` determinant-product bound.
  `hessenberg4NoPivotEntrywisePerturbation_det_eq_diag_prod_of_upperHessenberg`
  and `hessenberg4NoPivotRoundedTrace_nearbyDet_relError_le_gamma` now provide
  that determinant-product certificate for the generic 4-by-4 nearby matrix
  under explicit nonzero-pivot hypotheses. This still does not prove a primitive
  floating-point GE trace deriving Table 1.3.
  `hessenbergDetExampleTable13StoredAlpha`,
  `hessenbergDetExampleTable13StoredMatrix`,
  `hessenbergDetExampleTable13StoredRhs`,
  `hessenbergDetExampleTable13StoredAlpha_eq`,
  `hessenbergDetExampleTable13StoredAlpha_ne_zero`,
  `hessenbergDetExampleTable13_storedMatrix_eq_storedAlpha_matrix`,
  `hessenbergDetExampleTable13StoredMatrix_det_eq_noPivotUDiag_prod`, and
  `hessenbergDetExampleTable13_round_one_div_storedAlpha`,
  `hessenbergDetExampleTable13StoredMatrix_firstMultiplier_rounds_to_ten_pow_seven`,
	  `hessenbergDetExampleTable13_round_ten_pow_seven_mul_neg_one`,
	  `hessenbergDetExampleTable13StoredMatrix_firstStage_diag11_rounds_to`,
	  `hessenbergDetExampleTable13StoredMatrix_firstStage_super12_rounds_to`,
	  `hessenbergDetExampleTable13StoredMatrix_firstStage_super13_rounds_to`,
	  `hessenbergDetExampleTable13_round_one_div_firstStageDiag`,
	  `hessenbergDetExampleTable13StoredMatrix_secondMultiplier_rounds_to`,
	  `hessenbergDetExampleTable13_round_secondMultiplier_mul_firstStageSuper`,
	  `hessenbergDetExampleTable13_round_one_sub_secondStageProduct`,
	  `hessenbergDetExampleTable13_round_neg_one_sub_secondStageProduct`,
	  `hessenbergDetExampleTable13StoredMatrix_secondStage_diag22_rounds_to`,
	  `hessenbergDetExampleTable13StoredMatrix_secondStage_super23_rounds_to`,
	  `hessenbergDetExampleTable13_round_one_div_secondStageDiag`,
	  `hessenbergDetExampleTable13_round_thirdMultiplier_mul_secondStageSuper`,
		  `hessenbergDetExampleTable13_round_one_sub_thirdStageProduct`,
		  `hessenbergDetExampleTable13StoredMatrix_thirdMultiplier_rounds_to`,
		  `hessenbergDetExampleTable13StoredMatrix_finalDiag_rounds_to`,
		  `hessenbergDetExampleTable13_storedRhs_rows`,
			  `hessenbergDetExampleTable13_round_sourceAlpha_sub_three`,
			  `hessenbergDetExampleTable13StoredRhs0_eq_neg_three`,
			  `hessenbergDetExampleTable13StoredRhs_firstStage_rhs1_rounds_to`,
			  `hessenbergDetExampleTable13StoredRhs_secondStage_rhs2_rounds_to`, and
			  `hessenbergDetExampleTable13StoredRhs_finalStage_rhs3_rounds_to` close only the binary32 input,
			  stored-exact-determinant, first-multiplier-division, first-row-update, and
			  no-pivot elimination diagonal/determinant-product plus forward-RHS-update adapter: they separate the source real `10^-7` from
		  `fl32(10^-7)=14073749/2^47`, keep the exactly representable `0`, `1`, `-1`,
		  and `2` entries fixed, prove the first stored pivot is nonzero, prove the
	  stored matrix exact determinant equals its no-pivot diagonal product, prove
	  `fl32(1/fl32(alpha)) = 10^7`, prove the first-stage row update entries
	  `10000001`, `9999999`, and `9999999`, prove
	  `fl32(1/10000001)=14073747/2^47`, prove
		  `fl32((14073747/2^47)*9999999)=4194303/4194304` and the corresponding
			  `(2,2)`/`(2,3)` updates `1/4194304` and `-8388607/4194304`, prove the final
			  multiplier `4194304` and final diagonal `8388608`, prove the left-to-right
				  determinant product `8388609/4194304` and its exact relative error
				  `12589/655360065536`, prove `fl32(alpha-3)=-3`, and prove the forward
				  RHS elimination updates `30000000`, `-4194303/2097152`, and `8388608`.
				  They do not prove the downstream back substitution values printed in
				  Table 1.3.
  `hessenbergDetRoundedProduct_relError_le_gamma` assumes the per-product
  factors satisfy `|eta_i| <= fp.u`, assumes `gammaValid fp n`, and assumes
  the computed diagonal product is nonzero.
  `hessenbergDetRoundedProduct_relError_le_gamma_of_det_eq_diag_prod` lifts
  this bound to an exact matrix determinant once `det(A)` is proved equal to
  that diagonal product.
- `hessenbergDetExampleNoPivotUDiag_prod_eq`,
  `hessenbergDetExampleMatrix_det_eq_noPivotUDiag_prod`, and
  `hessenbergDetExampleMatrix_det_eq` assume `alpha != 0` and
  `alpha + 1 != 0` because the displayed no-pivot diagonal entries and
  elimination multipliers contain those denominators. They prove exact
  determinant preservation and diagonal-product algebra for the displayed
  example. `hessenbergDetExampleRoundedProduct_relError_le_gamma` and
  `hessenbergDetExample_alpha_ten_pow_roundedProduct_relError_le_gamma` close
  the determinant-product relative-error bridge for the displayed family and
  source value, respectively, but do not prove the nearby-matrix
  determinant-product certificate for the full GE path or derive the Table 1.3
  entries from a primitive
  single-precision trace.
- `hessenbergDetExampleMatrixInv_alpha_ten_pow_isInverse`,
  `hessenbergDetExample_kappaInfProduct_alpha_ten_pow_eq`, and
  `hessenbergDetExample_kappaInfProduct_alpha_ten_pow_near_sixteen` close the
  exact inverse and condition-number layer for `alpha=10^-7`; they do not prove
  the primitive-operation single-precision solve trace.
  `hessenbergDetExampleMatrix_alpha_ten_pow_det_eq`,
  `hessenbergDetExampleMatrix_alpha_ten_pow_det_near_two`, and
  `hessenbergDetExample_alpha_ten_pow_exact_table_baseline` separately close
  the exact source-value determinant and exact Table 1.3 baseline. The
  `hessenbergDetExampleTable13_*` row/relative-error theorems close the printed
  Table 1.3 data and contrast as exact rational table facts. The residual
  theorems insert the displayed computed solution into the exact source system
  and prove residual rows `[-1.3842e-7,-1.3842,0,0]`, residual norm `1.3842`,
  and scaled residual `6921/47684 > 0.1`; they still do not derive the
  displayed solution from a primitive single-precision GE trace. The theorem
  `hessenbergDetExampleFirstMultiplier_alpha_ten_pow` separately proves the
  exact first multiplier for the same source value.
- `kahanRationalFunction` uses Lean's total real division. The theorem
  `kahanHornerDenominator_grid_pos_of_one_le_of_le_three_sixty_one` proves the
  denominator is positive at all 361 exact source grid points, and
  `kahanHornerDenominator_gt_three_on_source_grid_interval` proves the full
  source interval denominator is bounded away from zero by `3`.
  `kahanRationalFunction_source_interval_variation_from_first_lt` and
  `kahanRationalFunction_grid_pair_variation_lt_two` are exact reference-curve
  bounds for the source interval and source grid. The `kahanContinuedFraction*`
  theorems now derive the continued-fraction reference expression, prove its
  intermediate denominators are nonzero on the source interval, and identify
  its 361 grid values with the exact rational-function reference values. The
  `flKahanHorner*` theorems now model the
  displayed Horner operation order in the abstract `FPModel` and expose the
  eight numerator, seven denominator, and one quotient local relative-error
  factors. The `ieeeDoubleKahan*` theorems instantiate the same operation order
  with `FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp` under
  explicit finite-normal primitive-result certificates. The source-interval and
  source-grid theorems now discharge the numerator, denominator, and final
  quotient-division certificates without enumerating the 361 points; they still
  do not prove the rounded nonrandom visual pattern.

## Proof Sources

No external source was used for the closed additions in this pass; the new
definitions and cancellation/Cramer/GEPP-residual proofs are direct
formalizations of the local PDF plus elementary determinant, inverse,
triangle-inequality, normwise conditioning algebra, exact rational arithmetic,
quadratic overflow-example scaling algebra, two-operation rounding/gamma algebra,
aggregate sample-variance arithmetic,
single-rounding power algebra, Frobenius/infinity-norm comparison, and
exact no-pivot LU, square-root/square iteration, and inverse-square
monotonicity algebra, the displayed HP 48G surrogate function, compact HP 48G
phase-law-to-surrogate bridge, and source-interval error arithmetic, and
the exact/modelled branch arithmetic and one concrete binary32 sine-plateau
base point in the §1.13 increasing-precision example, exact exp/log branch
algebra for §1.14.1, exact trigonometric
Givens-block orthogonality, two-component action, and ratio zeroing algebra
for §1.14.2, exact characteristic-determinant,
displayed-eigenvalue, terminating-binary/IEEE-double exact-storage obstruction,
row-sum/eigenvector algebra, first-step perturbation algebra, and exact
inverse-iteration shifted-system/eigenvector plus harmless-direction algebra
for §1.15, and exact upper-Hessenberg inverse, conditioning,
determinant-preservation, diagonal-product, and multiplier
algebra for §1.16, exact
Horner-form rational-function/grid/all-grid exact reference-variation algebra for §1.17, and
the elementary real/complex algebra behind Problem 1.4's stable
complex-square-root formulae, plus the exact digit-glyph arithmetic for
  Problem 1.6's calculator-word puzzle, finite-dimensional Cauchy-Schwarz,
  affine-mean, and finite-difference algebra for Problem 1.7's displayed
  componentwise/normwise condition-number closed forms, and
  finite-sum/cross-term cancellation plus triangle-inequality relative-error
  algebra for Problem 1.10's perturbed two-pass mean identity, one-factor
  rounded-transfer bound, and weighted nonnegative-sum aggregate-factor bridge,
  plus first-pass mean and fixed-supplied-mean subtraction/squaring/summation/
  division gamma algebra plus composed true-variance relative-error algebra and
  squared-`gamma` mean-error bounding plus linear-unit-roundoff gamma splitting
  for Problem 1.10's rounded second pass, and elementary
  linear-recurrence/geometric-limit
  algebra for Problem 1.8's Kahan-Muller recurrence and hidden `100^k` mode,
  plus finite rational interval arithmetic for Problem 1.2's near-integer table
  ambiguity.

The literal filter/limsup notation wrappers for the explicit Problem 1.7 and
Problem 1.10 quadratic remainders are now closed. A
full IEEE primitive-operation trace for Problem 1.8 if a named machine path is
required, the concrete Problem 1.5 exp/log routine instantiation and concrete
Fortran execution derivation of Table 1.1, plus later numerical examples should
receive proof-source rows before closure when the PDF supplies only a problem
statement or a qualitative discussion rather than a proof.

## Validation

Validation commands for this audit:

- `lake build LeanFpAnalysis.FP.Analysis.Accumulation`
- `lake build LeanFpAnalysis.FP.Analysis.BeneficialRounding`
- `lake build LeanFpAnalysis.FP.Analysis.CalculatorWords`
- `lake build LeanFpAnalysis.FP.Analysis.CancellationOfRoundingErrors`
- `lake build LeanFpAnalysis.FP.Analysis.ComplexSqrt`
- `lake build LeanFpAnalysis.FP.Analysis.CramersRule`
- `lake build LeanFpAnalysis.FP.Analysis.Error`
- `lake build LeanFpAnalysis.FP.Analysis.IncreasingPrecision`
- `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`
- `lake build LeanFpAnalysis.FP.Analysis.NearInteger`
- `lake build LeanFpAnalysis.FP.Analysis.NonrandomRounding`
- `lake build LeanFpAnalysis.FP.Analysis.ProblemDependentStability`
- `lake build LeanFpAnalysis.FP.Analysis.TrigCancellation`
- `lake build LeanFpAnalysis.FP.Analysis.Quadratic`
- `lake build LeanFpAnalysis.FP.Analysis.MullerRecurrence`
- `lake build LeanFpAnalysis.FP.Analysis.SampleVariance`
- `lake build LeanFpAnalysis.FP.Analysis.Stability`
- `lake build LeanFpAnalysis.FP.Analysis.PerturbationTheory`
- `lake build LeanFpAnalysis.FP.Algorithms.LU.GrowthFactor`
- `lake build LeanFpAnalysis.FP.Algorithms.QR.GivensSpec`
- `lake build LeanFpAnalysis.FP.Analysis`
- `lake env lean examples/LibraryLookup.lean`
- 2026-06-12 focused §1.12.3 continuation: reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`,
  `lake build LeanFpAnalysis.FP.Analysis.Chopping`,
  `lake build LeanFpAnalysis.FP.Analysis`, and
  `lake env lean examples/LibraryLookup.lean`.
- 2026-06-12 focused §1.12.3 axiom audit: `#print axioms` for
  `inverseSquareSingleEarlyMantissaPrefix_2895_eq`,
  `inverseSquareSingleEarlyMantissaPrefix_2895_add_base_eq_preWindow`,
  `inverseSquareSingleEarlyMantissaIncrementNearestCertificateBool_eq_true`,
  `inverseSquareSingleEarlyMantissaIncrementNearestCertificate`,
  `inverseSquareSingle_add_term_rounds_to_nearest_mantissa_of_scaled_bounds`,
  `inverseSquareSingleEarlyMantissaIncrementRule_closed`,
  `inverseSquareSingleForwardAccumulator_2896_eq_prePlateauWindowStart`,
  `inverseSquareSingleForwardAccumulator_2896_add_lt_plateau`,
  `inverseSquareSingleForwardAccumulator_4096_add_eq_plateau`,
  `inverseSquareSingleReverseAccumulatorFrom_add`,
  `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq`,
  `inverseSquareSingleReverseAccumulator_split`, and
  `inverseSquareSingleReverseAccumulator_ten_pow_nine_split_4096`,
  `inverseSquareReverseTenPowNineHighPrefix_index_ge_4097`, and
  `inverseSquareTerm_le_two_pow_neg_24_of_reverse_ten_pow_nine_high_prefix`;
  the pure
  integer-prefix certificates report only `[propext]`, the high-prefix index
  lemma reports only `[propext, Quot.sound]`, and the Real source-rounding
  bridge plus reverse structural/term-bound theorems report only `[propext,
  Classical.choice, Quot.sound]`.
- 2026-06-12 focused §1.12.3 reverse high-prefix continuation: reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`,
  `lake build LeanFpAnalysis.FP.Analysis`, and
  `lake env lean examples/LibraryLookup.lean`.  `#print axioms` for
  `inverseSquareExactReverseAccumulatorFrom_add_start`,
  `inverseSquareExactReverseAccumulatorFrom_add`,
  `inverseSquareExactReverseAccumulator_ten_pow_nine_split_4096`,
  `inverseSquareExactReverseAccumulator_ten_pow_nine_eq_highPrefix_add_low4096`,
  `inverseSquareTerm_nonneg`, `inverseSquareTerm_le_telescope`,
  `inverseSquareExactReverseAccumulatorFrom_le_telescope`,
  `inverseSquareExactReverseTenPowNineHighPrefix_le_inv_4096`, and
  `inverseSquareExactReverseAccumulator_ten_pow_nine_sub_low4096_le_inv_4096`
  reports only
  `[propext, Classical.choice, Quot.sound]`.
- 2026-06-12 focused §1.12.3 exact start-window squeeze: reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`,
  `lake build LeanFpAnalysis.FP.Analysis`, and
  `lake env lean examples/LibraryLookup.lean`.  `#print axioms` for
  `inverseSquareTerm_ge_telescope_succ`,
  `inverseSquareExactReverseAccumulatorFrom_ge_telescope_succ`,
  `inverseSquareExactReverseTenPowNineHighPrefix_ge_printedSuffixStartLower`,
  `inverseSquareExactReverseTenPowNineHighPrefix_le_printedSuffixStartUpper`,
  `inverseSquareExactReverseTenPowNineHighPrefix_mem_printedSuffixStartWindow`,
  and
  `inverseSquareExactReverseAccumulator_ten_pow_nine_sub_low4096_mem_printedSuffixStartWindow`
  reports only
  `[propext, Classical.choice, Quot.sound]`.
- 2026-06-12 focused §1.12.3 reverse printed-value reduction: reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`,
  `lake build LeanFpAnalysis.FP.Analysis`, full `lake build`, and
  `lake env lean examples/LibraryLookup.lean`.  `#print axioms` for
  `inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixWindow`,
  `inverseSquareSingleReverseSuffixWindowMapsToPrinted`,
  `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_window_certificates`,
  and
  `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_mem_window`
  reports only
  `[propext, Classical.choice, Quot.sound]`.
- 2026-06-12 focused §1.12.3 refined reverse window: added
  `inverseSquareSingleReverseSuffixStartUpperTight`, proved
  `inverseSquareExactReverseTenPowNineHighPrefix_le_printedSuffixStartUpperTight`
  and `inverseSquareExactReverseTenPowNineHighPrefix_mem_printedSuffixStartTightWindow`,
  proved the candidate membership
  `inverseSquareSingleReverseTenPowNineHighPrefixCandidate_mem_printedSuffixStartTightWindow`,
  and added the refined certificate predicates
  `inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow`
  and `inverseSquareSingleReverseTightSuffixWindowMapsToPrinted` plus their
  composition theorems.  This replaces the over-wide whole-window target with
  the tighter interval route; the remaining reverse gap is still the rounded
  high-prefix bridge or the refined tight-window suffix proof.  Reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`,
  `lake env lean examples/LibraryLookup.lean`, whitespace/no-forbidden-token
  hygiene, `git diff --check`, and `#print axioms` for the new refined-window
  theorems; the axiom report is only
  `[propext, Classical.choice, Quot.sound]`.
- 2026-06-12 focused §1.12.3 concrete reverse-candidate reduction: reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`,
  `lake build LeanFpAnalysis.FP.Analysis`, rebuilt
  `LeanFpAnalysis.FP.Algorithms.PairwiseSum` to refresh a stale lookup
  dependency, and reran `lake env lean examples/LibraryLookup.lean`.
  `#print axioms` for
  `inverseSquareSingleReverseTenPowNineHighPrefixCandidate_mem_printedSuffixStartWindow`,
  `inverseSquareSingleReverseTenPowNineHighPrefixEqCandidate`,
  `inverseSquareSingleReverseCandidateSuffixMapsToPrinted`,
  `inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixWindow_of_eq_candidate`,
  and
  `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_candidate_certificates`
  reports only `[propext, Classical.choice, Quot.sound]`.
- 2026-06-12 focused §1.12.3 after-`4096` suffix reduction: reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation` and
  `lake env lean examples/LibraryLookup.lean`.  `#print axioms` for
  `inverseSquareSingleReverseAfter4096Candidate`,
  `inverseSquareSingleReverseCandidate_add_4096_term_rounds_to_after4096`,
  `inverseSquareSingleReverseAfter4096SuffixMapsToPrinted`, and
  `inverseSquareSingleReverseCandidateSuffixMapsToPrinted_of_after4096`
  reports only `[propext, Classical.choice, Quot.sound]`.  A rerun of
  `lake build LeanFpAnalysis.FP.Analysis` during this continuation failed in
  the unrelated untracked module `LeanFpAnalysis/FP/Analysis/Counting.lean`,
  before reaching any new Chapter 1 obligation.
- 2026-06-12 focused §1.12.3 after-`4095` suffix anchor: reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation` and
  `lake env lean examples/LibraryLookup.lean`.  `#print axioms` for
  `inverseSquareSingleReverseAfter4095Candidate`,
  `inverseSquareSingleReverseAfter4096_add_4095_term_rounds_to_after4095`,
  `inverseSquareSingleReverseAfter4095SuffixMapsToPrinted`, and
  `inverseSquareSingleReverseAfter4096SuffixMapsToPrinted_of_after4095`
  reports only `[propext, Classical.choice, Quot.sound]`.
  The second anchor is deliberately not a plan to prove the remaining suffix
  step by step; it validates the post-`4096` state encoding and reduces the
  open suffix target to a compact after-`4095` trace certificate.
- 2026-06-12 focused §1.12.3 compact suffix-certificate bridge: added
  `inverseSquareSingleForwardStep_eq_left_of_adjacent_strict_between_left_closer`
  and
  `inverseSquareSingleForwardStep_eq_right_of_adjacent_strict_between_right_closer`
  to factor the positive finite-normal-range and nearest/even adjacent-bracket
  reasoning out of concrete suffix steps.  The after-`4095` anchor now uses the
  left-endpoint bridge, making the next suffix target a compact certificate
  problem rather than a list of thousands of copied local rounding proofs.
  Reran `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`
  and `lake env lean examples/LibraryLookup.lean`; both passed.  `#print axioms`
  for the two bridge theorems and the refactored after-`4095` anchor reports
  only `[propext, Classical.choice, Quot.sound]`.
- 2026-06-12 focused §1.12.3 arbitrary-scale suffix step certificate: added
  `inverseSquareSingle_scaleAtExponent_mul_two_pow`,
  `inverseSquareSingle_scaleAtExponent_eq_two_div_two_pow`, and
  `inverseSquareSingleForwardStep_normalizedValue_nearest_mantissa_of_scaled_bounds_at_scale`.
  The after-`4095` anchor now reduces to the integer half-cell inequalities
  `(2*2049-1)*4095^2 < 2^36` and
  `2^36 < (2*2049+1)*4095^2`, plus mantissa/exponent range checks.  This is
  the intended shape for exponent-band suffix chunks.  Reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation` and
  `lake env lean examples/LibraryLookup.lean`; both passed.  `#print axioms`
  for the scale identities, the arbitrary-scale certificate theorem, and the
  refactored after-`4095` anchor reports only
  `[propext, Classical.choice, Quot.sound]`.
- 2026-06-12 focused §1.12.3 first after-`4095` same-exponent band
  certificate: added `inverseSquareSingleReverseBefore2048Candidate`,
  `inverseSquareSingleReverseAfter4095Prefix_4094_to_2049_eq`,
  `inverseSquareSingleReverseAfter4095Band4094To2049CertificateBool_eq_true`,
  `inverseSquareSingleReverseAfter4095Band4094To2049Certificate`,
  `inverseSquareSingleReverseAfter4095Accumulator_4094_bandPrefix_of_le`,
  `inverseSquareSingleReverseAfter4095Accumulator_4094_to_before2048`, and
  `inverseSquareSingleReverseAfter4095SuffixMapsToPrinted_of_before2048`.
  This closes the 2046 same-exponent additions `4094^{-2}, ..., 2049^{-2}`
  by a compact checked prefix certificate and reduces the remaining concrete
  suffix target to `inverseSquareSingleReverseBefore2048SuffixMapsToPrinted`.
  Reran `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`
  and `lake env lean examples/LibraryLookup.lean`; both passed.  `#print axioms`
  for the prefix equality, Boolean certificate, band induction, band endpoint,
  and suffix-reduction theorem reports only
  `[propext, Classical.choice, Quot.sound]`.
- 2026-06-12 focused §1.12.3 before-`2048` boundary and next same-exponent
  band: added the reusable
  `inverseSquareSingleReverseAccumulatorFrom_scaledBandPrefix_of_le`, the
  after-`2048` and before-`1024` candidates, the midpoint/even boundary theorem
  `inverseSquareSingleReverseBefore2048_add_2048_term_rounds_to_after2048`,
  the 1023-entry checked band certificate through
  `inverseSquareSingleReverseAfter2048Accumulator_2047_to_before1024`, and the
  suffix-reduction theorem
  `inverseSquareSingleReverseBefore2048SuffixMapsToPrinted_of_before1024`.
  This reduces the remaining concrete suffix target to
  `inverseSquareSingleReverseBefore1024SuffixMapsToPrinted`.  Reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation` and
  `lake env lean examples/LibraryLookup.lean`; both passed.  `#print axioms`
  for the generic band theorem, the `2048` boundary step, the prefix equality,
  the Boolean certificate, the band induction, the band endpoint, and the
  suffix-reduction theorem reports only
  `[propext, Classical.choice, Quot.sound]`.
- 2026-06-12 focused §1.12.3 before-`1024` boundary and next same-exponent
  band: added the after-`1024` and before-`512` candidates, the exact
  representable boundary theorem
  `inverseSquareSingleReverseBefore1024_add_1024_term_rounds_to_after1024`,
  the 511-entry checked band certificate through
  `inverseSquareSingleReverseAfter1024Accumulator_1023_to_before512`, and the
  suffix-reduction theorem
  `inverseSquareSingleReverseBefore1024SuffixMapsToPrinted_of_before512`.
  This reduces the remaining concrete suffix target to
  `inverseSquareSingleReverseBefore512SuffixMapsToPrinted` and keeps the
  reverse proof in compact boundary/band form, not one theorem per summand.
  Reran `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`;
  it passed.  Rebuilt the stale lookup dependency
  `LeanFpAnalysis.FP.Algorithms.DoublyCompensatedSum` and reran
  `lake env lean examples/LibraryLookup.lean`; both passed.  `#print axioms`
  for the `1024` boundary step, prefix equality, Boolean certificate, band
  induction, band endpoint, and suffix-reduction theorem reports only
  `[propext]` for the pure computed certificates and
  `[propext, Classical.choice, Quot.sound]` for the Real/finite-format proof
  theorems.
- 2026-06-12 focused §1.12.3 before-`512` boundary and next same-exponent
  band: added the after-`512` and before-`256` candidates, the midpoint/even
  boundary theorem
  `inverseSquareSingleReverseBefore512_add_512_term_rounds_to_after512`, the
  255-entry checked band certificate through
  `inverseSquareSingleReverseAfter512Accumulator_511_to_before256`, and the
  suffix-reduction theorem
  `inverseSquareSingleReverseBefore512SuffixMapsToPrinted_of_before256`.  This
  reduces the remaining concrete suffix target to
  `inverseSquareSingleReverseBefore256SuffixMapsToPrinted` and continues the
  compact boundary/band proof shape.  Reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`; it
  passed.  Rebuilt the stale lookup dependency
  `LeanFpAnalysis.FP.Algorithms.CompensatedSum` and reran
  `lake env lean examples/LibraryLookup.lean`; both passed.  `#print axioms`
  for the `512` boundary step, prefix equality, Boolean certificate, band
  induction, band endpoint, and suffix-reduction theorem reports only
  `[propext]` for the pure computed certificates and
  `[propext, Classical.choice, Quot.sound]` for the Real/finite-format proof
  theorems.
- 2026-06-12 focused §1.12.3 before-`256` boundary and next same-exponent
  band: added the after-`256` and before-`128` candidates, the midpoint/even
  boundary theorem
  `inverseSquareSingleReverseBefore256_add_256_term_rounds_to_after256`, the
  127-entry checked band certificate through
  `inverseSquareSingleReverseAfter256Accumulator_255_to_before128`, and the
  suffix-reduction theorem
  `inverseSquareSingleReverseBefore256SuffixMapsToPrinted_of_before128`.  This
  reduces the remaining concrete suffix target to
  `inverseSquareSingleReverseBefore128SuffixMapsToPrinted` and continues the
  compact boundary/band proof shape.  Reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation` and
  `lake env lean examples/LibraryLookup.lean`; both passed.  `#print axioms`
  for the `256` boundary step, prefix equality, Boolean certificate, band
  induction, band endpoint, and suffix-reduction theorem reports only
  `[propext]` for the pure computed certificates and
  `[propext, Classical.choice, Quot.sound]` for the Real/finite-format proof
  theorems.
- 2026-06-12 focused §1.12.3 before-`128` boundary and next same-exponent
  band: added the after-`128` and before-`64` candidates, the midpoint/even
  boundary theorem
  `inverseSquareSingleReverseBefore128_add_128_term_rounds_to_after128`, the
  63-entry checked band certificate through
  `inverseSquareSingleReverseAfter128Accumulator_127_to_before64`, and the
  suffix-reduction theorem
  `inverseSquareSingleReverseBefore128SuffixMapsToPrinted_of_before64`.  This
  reduces the remaining concrete suffix target to
  `inverseSquareSingleReverseBefore64SuffixMapsToPrinted` and continues the
  compact boundary/band proof shape.  Reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation` and
  the new-theorem `#print axioms` audit; the theorem dependencies match the
  established profile: `[propext]` for pure computed certificates and
  `[propext, Classical.choice, Quot.sound]` for Real/finite-format proof
  theorems.
- 2026-06-12 focused §1.12.3 before-`64` boundary and next same-exponent band:
  added the after-`64` and before-`32` candidates, the midpoint/even boundary
  theorem `inverseSquareSingleReverseBefore64_add_64_term_rounds_to_after64`,
  the 31-entry checked band certificate through
  `inverseSquareSingleReverseAfter64Accumulator_63_to_before32`, and the
  suffix-reduction theorem
  `inverseSquareSingleReverseBefore64SuffixMapsToPrinted_of_before32`.  This
  reduces the remaining concrete suffix target to
  `inverseSquareSingleReverseBefore32SuffixMapsToPrinted` and continues the
  compact boundary/band proof shape.  Reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`;
  rebuilt the stale `LeanFpAnalysis.FP.Analysis.Problem2_3` lookup dependency;
  reran `lake env lean examples/LibraryLookup.lean`; and reran the new-theorem
  `#print axioms` audit, with only `[propext]` for pure computed certificates
  and `[propext, Classical.choice, Quot.sound]` for Real/finite-format proof
  theorems.
- 2026-06-12 focused §1.12.3 final concrete low-index suffix closure: added
  the after-`32`, before-`16`, after-`16`, before-`8`, after-`8`, before-`4`,
  after-`4`, after-`3`, and after-`2` candidate states; closed the exact
  `32^{-2}` and `8^{-2}` boundary steps, the `16^{-2}` midpoint/even boundary
  step, the compact checked bands `31^{-2}, ..., 17^{-2}`,
  `15^{-2}, ..., 9^{-2}`, and `7^{-2}, 6^{-2}, 5^{-2}`, and the final
  explicit additions `4^{-2}, 3^{-2}, 2^{-2}, 1^{-2}`.  The theorem
  `inverseSquareSingleReverseCandidateSuffixMapsToPrinted_closed` now closes
  the concrete suffix from the named high-prefix candidate to Higham's printed
  binary32 reverse accumulator, and
  `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_eq_candidate`
  reduces the full reverse-order printed value to the separate high-prefix
  equality certificate.  Reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation` and
  `lake env lean examples/LibraryLookup.lean`; both passed.  Reran the
  new-theorem `#print axioms` audit, with only `[propext]` for pure computed
  certificates and `[propext, Classical.choice, Quot.sound]` for
  Real/finite-format proof theorems.
- 2026-06-12 focused §1.11 Table 1.1 finite-data layer: added
  `expOneApproxTable11N`, `expOneApproxTable11Computed`, and
  `expOneApproxTable11RelativeError`, with row theorems
  `expOneApproxTable11_n_rows`, `expOneApproxTable11_computed_rows`, and
  `expOneApproxTable11_relativeError_rows`.  These close the displayed table
  data as exact rational rows only; concrete Fortran execution and libm/IEEE
  exp/log routine derivations remain open.  Reran
  `lake build LeanFpAnalysis.FP.Analysis.Accumulation`,
  `lake env lean examples/LibraryLookup.lean`, and the new-theorem
  `#print axioms` audit; the axiom report is only
  `[propext, Classical.choice, Quot.sound]`.  Reran no-forbidden-token,
  trailing-whitespace, and diff-check hygiene for the touched Table 1.1 files;
  all were clean.
- 2026-06-13 focused §1.11 single-rounded-base relative-error formula: added
  `expOneApproxRoundedBase_relError_eq_initial_error_pow_abs`.  This sharpens
  the existing single-initial-rounding mechanism by proving that, under exact
  exponentiation after the first rounded formation of `1+1/n`, the relative
  error is exactly `|(1+delta)^n - 1|` for some `|delta| <= fp.u`.  This is a
  uniform theorem over all `n`, not a case-by-case Table 1.1 replay.  Reran
  `lake build LeanFpAnalysis.FP.Analysis.Accumulation` and
  `lake env lean examples/LibraryLookup.lean`; both passed, with lookup output
  length 55,725 lines.  Reran the new-theorem `#print axioms` audit; the axiom
  report is `[propext, Classical.choice, Quot.sound]`.  Reran no-forbidden-token,
  trailing-whitespace, and diff-check hygiene for the touched files; all were
  clean.
- 2026-06-12 focused §1.11 Strassen threshold-count substrate: added
  `strassenLeafMulCount`, `strassenThresholdDimension`,
  `strassenThresholdDimension_halve_leaf_succ`,
  `strassenLeafMulCount_threshold_halving_decreases`, and
  `strassenThresholdHalving_same_dimension_and_decreases_count`.  These close
  the exact dominant leaf-multiplication count part of the Strassen paragraph:
  one more recursion level keeps the represented matrix dimension fixed while
  halving the classical leaf threshold and strictly reducing the dominant leaf
  multiplication count.  The empirical threshold-error-growth claim remains
  open.  Reran `lake build LeanFpAnalysis.FP.Analysis.Accumulation`, rebuilt
  the stale lookup dependency `LeanFpAnalysis.FP.Analysis.Problem2_3`, reran
  `lake env lean examples/LibraryLookup.lean`, and reran the new-theorem
  `#print axioms` audit; the axiom report is `[propext]` for the dimension
  identity and `[propext, Classical.choice, Quot.sound]` for the two count
  decrease theorems.  Reran no-forbidden-token, trailing-whitespace, and
  diff-check hygiene for the touched Strassen-count files; all were clean.
- 2026-06-12 focused §1.10.1 Cramer/GEPP displayed MATLAB finite data: added
  `cramerGeppExampleCramerSolution`, `cramerGeppExampleCramerResidual`,
  `cramerGeppExampleGeppSolution`, `cramerGeppExampleGeppResidual`, and
  `cramerGeppExampleAccurateVector`, plus row-equality theorems and
  `cramerGeppExample_residual_component_gap`.  A later visual audit corrected
  the interpretation of the table header: these entries are the printed
  scaled-residual column `r/(||A||_2||xhat||_2)`, not raw residuals.  The
  source-facing `...ScaledResidual...` aliases and gap theorems now record that
  correction.  The hidden MATLAB system reconstruction, raw residual vector,
  exact solution, and condition-number provenance remain open.  Reran
  `lake build LeanFpAnalysis.FP.Analysis.CramersRule`,
  `lake env lean examples/LibraryLookup.lean`, and the new-theorem
  `#print axioms` audit; the axiom report is
  `[propext, Classical.choice, Quot.sound]` for the row and component-gap
  theorems.  Reran no-forbidden-token, trailing-whitespace, and diff-check
  hygiene for the touched Cramer/GEPP files; all were clean.
- 2026-06-13 focused §1.10.1 Cramer/GEPP printed scaled-residual norm layer:
  added
  `cramerGeppExample_cramerResidual_infNorm_eq`,
  `cramerGeppExample_geppResidual_infNorm_eq`, and
  `cramerGeppExample_residual_infNorm_gap` under the legacy residual-column
  names.  A later visual audit corrected the interpretation: the displayed
  column is already scaled by `||A||_2||xhat||_2`.  The source-facing aliases
  `cramerGeppExample_cramerScaledResidual_infNorm_eq`,
  `cramerGeppExample_geppScaledResidual_infNorm_eq`, and
  `cramerGeppExample_scaledResidual_infNorm_gap` now state the same checked
  facts with accurate names, and `cramerGeppExample_scaledResidual_vecNorm2Sq_gap`
  gives the squared 2-norm version.  The hidden MATLAB matrix/RHS, exact
  solution, raw residual vector, and `K_2(A)` provenance remain open if that
  generation path is required. Reran
  `lake build LeanFpAnalysis.FP.Analysis.CramersRule`; it exited successfully.
  Reran `lake env lean examples/LibraryLookup.lean`, with output redirected to
  `/private/tmp/librarylookup-ch1-cramer-residual-norm.out`; it exited
  successfully and produced 50428 lines. The focused axiom audit for the three
  new residual-norm theorems reports `[propext, Classical.choice, Quot.sound]`.
  Reran no-forbidden-token, trailing-whitespace, and diff-check hygiene for the
  touched Cramer/GEPP files; all were clean.
- 2026-06-12 focused §1.13 supplied two-precision failure bridge: added
  `increasingPrecisionExampleElse_two_precision_failure_of_expHat_one`.  This
  proves that two modeled precision runs, each entering the else branch with
  nonzero `y` and supplied rounded exponential value `1`, both return `0` and
  both have relative error `1` against the exact value `f(2/3) = 1`.  The
  concrete Fortran single/double machine derivation, Hilbert/Pascal plots,
  sine-example binary plateau, and broader monotonicity/precision-relationship
  caveats remain open.  Reran
  `lake build LeanFpAnalysis.FP.Analysis.IncreasingPrecision`, refreshed the
  stale lookup dependencies `LeanFpAnalysis.FP.Algorithms.InsertionSum` and
  `LeanFpAnalysis.FP.Analysis.Problem2_3`, reran
  `lake env lean examples/LibraryLookup.lean`, and reran the new-theorem
  `#print axioms` audit; the axiom report is
  `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 focused §1.13 stored-input branch bridge: added
  `increasingPrecisionExampleY_ne_zero_of_ne_two_thirds`,
  `increasingPrecisionExampleY_pos_of_ne_two_thirds`, and
  `increasingPrecisionExampleElse_two_precision_failure_of_stored_inputs_expHat_one`.
  These prove that any stored input different from exact `2/3` has positive
  branch variable and therefore feeds the existing supplied `exp(y)=1`
  two-precision failure bridge, without enumerating precision cases.  Reran
  `lake build LeanFpAnalysis.FP.Analysis.IncreasingPrecision`; it exited
  successfully.  Reran `lake env lean examples/LibraryLookup.lean`, with
  output redirected to
  `/private/tmp/librarylookup-ch1-increasing-precision-branch.out`; it exited
  successfully and produced 50474 lines.  The focused axiom audit for the three
  new theorems reports `[propext, Classical.choice, Quot.sound]`.  Reran
  no-forbidden-token, trailing-whitespace, and diff-check hygiene for the
  touched IncreasingPrecision/lookup/ledger files; all were clean.  The
  concrete stored values and correctly rounded finite `exp(y)` selector trace
  were still open at that point; they are superseded by the 2026-06-14
  concrete finite-exp trace entry below.
- 2026-06-14 focused §1.13 finite IEEE stored-input obstruction: added
  `three_not_dvd_two_pow_nat`, `two_thirds_not_binaryTerminating`,
  `ieeeSingleFormat_normalizedSystem_binaryTerminating`,
  `ieeeSingleFormat_subnormalSystem_binaryTerminating`,
  `ieeeSingleFormat_finiteSystem_binaryTerminating`,
  `two_thirds_not_ieeeSingleFiniteSystem`,
  `two_thirds_not_ieeeDoubleFiniteSystem`,
  `increasingPrecisionExampleElse_two_precision_failure_of_ieee_finite_stored_inputs_expHat_one`,
  and
  `increasingPrecisionExampleElse_two_precision_failure_of_ieee_roundToEven_stored_source_expHat_one`.
  These close the binary-storage part of the Fortran branch example without
  enumerating precision cases: exact `2/3` is not terminating binary, every
  finite IEEE-single or IEEE-double value is terminating binary, and therefore
  neither format can store exact `2/3` as a finite value.  The source-shaped
  round-to-even wrapper applies the existing supplied-`exp(y)=1` two-run
  failure theorem to the single and double stored source inputs.  Reran
  `lake build LeanFpAnalysis.FP.Analysis.BeneficialRounding` and
  `lake build LeanFpAnalysis.FP.Analysis.IncreasingPrecision`; both exited
  successfully.  Rebuilt stale lookup dependencies
  `LeanFpAnalysis.FP.Analysis.CancellationOfRoundingErrors`,
  `LeanFpAnalysis.FP.Analysis.Problem2_27`, and
  `LeanFpAnalysis.FP.Analysis.NonrandomRounding`, then reran
  `lake env lean examples/LibraryLookup.lean`, with output redirected to
  `/private/tmp/librarylookup-ch1-increasing-precision-storage.out`; it exited
  successfully and produced 58047 lines.  The focused axiom audit for the seven
  new theorem declarations reports `[propext, Classical.choice, Quot.sound]`.
  Reran no-forbidden-token, trailing-whitespace, and diff-check hygiene for the
  touched BeneficialRounding/IncreasingPrecision/lookup/ledger files; all were
  clean.  The exact stored values and correctly rounded finite-exp trace are
  closed by the subsequent 2026-06-14 entry; an unspecified hidden vendor
  Fortran/libm `exp(y)` routine remains open.
- 2026-06-14 focused §1.13 concrete correctly rounded finite-exp trace: added
  `increasingPrecision_ieeeSingle_roundToEven_two_thirds`,
  `increasingPrecision_ieeeDouble_roundToEven_two_thirds`,
  `increasingPrecisionExampleY_ieeeSingle_roundToEven_two_thirds`,
  `increasingPrecisionExampleY_ieeeDouble_roundToEven_two_thirds`,
  `increasingPrecision_ieeeSingle_roundToEven_exp_branch_y_eq_one`,
  `increasingPrecision_ieeeDouble_roundToEven_exp_branch_y_eq_one`, and
  `increasingPrecisionExampleElse_two_precision_failure_of_ieee_roundToEven_stored_exp_source`.
  These prove the concrete round-to-even stored single/double values of source
  input `2/3`, compute the resulting branch variables as `2^-24/25` and
  `2^-53/25`, prove correctly rounded finite-format exponentials of both
  variables are exactly `1` using `|exp y - 1| <= 2|y|`, and close the
  single/double modeled branch failure without a supplied `exp(y)=1`
  hypothesis.  Reran
  `lake build LeanFpAnalysis.FP.Analysis.IncreasingPrecision`,
  `lake build LeanFpAnalysis.FP.Analysis.BeneficialRounding`, and
  `lake env lean examples/LibraryLookup.lean`, with output redirected to
  `/private/tmp/librarylookup-ch1-increasing-precision-concrete-exp.out`; the
  lookup exited successfully and produced 58100 lines.  The focused axiom audit
  for the eight concrete stored/exp theorem declarations reports
  `[propext, Classical.choice, Quot.sound]`.  Reran no-forbidden-token,
  trailing-whitespace, and diff-check hygiene for the touched
  BeneficialRounding/IncreasingPrecision/lookup/ledger files; all were clean.
  This is a repository-model correctly rounded finite selector trace, not a
  certificate for an unspecified vendor `exp` routine.
- 2026-06-13 focused §1.13 sine finite-format spacing certificate: added
  `finiteRoundToEven_eq_of_strict_closest`,
  `increasingPrecisionSinExample_finiteRoundToEven_eq_base_of_two_abs_scale_lt_spacing`,
  and
  `increasingPrecisionSinExampleSource_finiteRoundToEven_eq_base_of_spacing`.
  These reduce the binary-rounding plateau for
  `x+10^-8*sin(2^24*x)` to a local finite-format spacing certificate
  `2*10^-8 < |z-x|` for every other finite-format value `z`, rather than an
  input enumeration.  Reran
  `lake build LeanFpAnalysis.FP.Analysis.IncreasingPrecision`; it exited
  successfully.  Reran `lake env lean examples/LibraryLookup.lean >
  /private/tmp/librarylookup-ch1-increasing-precision-spacing.out`; it exited
  successfully and produced 55657 lookup lines.  The focused axiom audit for
  the three theorem surfaces reports only
  `[propext, Classical.choice, Quot.sound]`.
- 2026-06-14 focused §1.13 sine binary32 base-point plateau: added
  `increasingPrecisionSinExampleSource_ieeeSingle_roundToEven_one`, proving
  that `finiteRoundToEven` for IEEE single returns exactly `1` on the source
  expression `1+10^-8*sin(2^24*1)`. The proof uses the perturbation bound and
  the adjacent binary32 endpoints around `1`, not an input enumeration. Reran
  `lake build LeanFpAnalysis.FP.Analysis.IncreasingPrecision`; it exited
  successfully. Reran `lake env lean examples/LibraryLookup.lean` with output
  redirected to `/private/tmp/librarylookup-ch1-sine-x1.out`; it exited
  successfully and produced `58296` lookup lines. The focused axiom audit for
  the new declaration reports `[propext, Classical.choice, Quot.sound]`.
- 2026-06-14 focused §1.13 `x = 1/7` finite-storage obstruction: added
  `seven_not_dvd_two_pow_nat`, `one_seventh_not_binaryTerminating`,
  `one_seventh_not_ieeeSingleFiniteSystem`, and
  `one_seventh_not_ieeeDoubleFiniteSystem`. These prove the sine example's
  source rational `1/7` is not a terminating binary fraction and hence is not
  exactly a finite IEEE-single or IEEE-double value. Reran
  `lake build LeanFpAnalysis.FP.Analysis.BeneficialRounding` and
  `lake build LeanFpAnalysis.FP.Analysis.IncreasingPrecision`; both exited
  successfully. A focused `#check` file importing
  `LeanFpAnalysis.FP.Analysis.BeneficialRounding` recognizes all four new
  declarations, and the focused axiom audit reports
  `[propext, Classical.choice, Quot.sound]` for each. The full
  `examples/LibraryLookup.lean` rerun is currently blocked before reaching
  these new checks because rebuilding the aggregate `LeanFpAnalysis.FP.Analysis`
  target fails in the unrelated Chapter 2 file
  `LeanFpAnalysis/FP/Analysis/Problem2_10.lean`.
- 2026-06-14 focused §1.13 concrete `x = 1/7` stored values and errors: added
  `increasingPrecision_ieeeSingle_roundToEven_one_seventh`,
  `increasingPrecision_ieeeDouble_roundToEven_one_seventh`,
  `increasingPrecision_ieeeSingle_roundToEven_one_seventh_error`, and
  `increasingPrecision_ieeeDouble_roundToEven_one_seventh_error`, proving by
  adjacent finite endpoints that IEEE single stores source input `1/7` as
  `9586981*2^-26` with error `3/(7*2^26)` and IEEE double stores it as
  `5146971002709138*2^-55` with error `-2/(7*2^55)`. Reran
  `lake build LeanFpAnalysis.FP.Analysis.IncreasingPrecision`; it exited
  successfully. A focused `#check` file importing
  `LeanFpAnalysis.FP.Analysis.IncreasingPrecision` recognizes all four new
  declarations, and the focused axiom audit reports
  `[propext, Classical.choice, Quot.sound]` for each.
- 2026-06-14 focused §1.13 dyadic `1/7` early-precision representation
  dominance: added `increasingPrecision_one_seventh_binary_grid_abs_error_ge`
  `increasingPrecision_one_seventh_binary_grid_abs_error_gt_scale_of_t_le_twenty`,
  `increasingPrecision_one_seventh_binary_grid_abs_error_gt_scale_of_t_le_twenty_three`,
  `increasingPrecision_one_seventh_binary_grid_lower_bound_lt_scale_at_twenty_four`,
  `increasingPrecisionSinExampleSource_perturbation_lt_one_seventh_binary_grid_error_of_t_le_twenty`,
  and
  `increasingPrecisionSinExampleSource_perturbation_lt_one_seventh_binary_grid_error_of_t_le_twenty_three`.
  The first theorem proves uniformly that every dyadic `z/2^t` is at least
  `1/(7*2^t)` away from exact `1/7`; the threshold theorems prove that for
  `t <= 23` this representation lower bound is larger than the source sine
  amplitude `10^-8`, while at `t = 24` the universal lower bound has already
  fallen below that amplitude; and the perturbation theorems prove the source
  sine perturbation is smaller than the representation error throughout those
  early-precision ranges. Reran
  `lake build LeanFpAnalysis.FP.Analysis.IncreasingPrecision`; it exited
  successfully. A focused `#check` file importing
  `LeanFpAnalysis.FP.Analysis.IncreasingPrecision` recognizes all six declarations,
  and the focused axiom audit reports `[propext, Classical.choice, Quot.sound]`
  for each.
- 2026-06-13 focused Problem 1.10 named higher-order remainder: added
  `flSampleVarianceTwoPassProblem110MeanQuadraticBound`,
  `flSampleVarianceTwoPassProblem110Remainder`,
  `flSampleVarianceTwoPassProblem110MeanQuadraticBound_nonneg`,
  `flSampleVarianceTwoPassProblem110Remainder_nonneg`, and
  `flSampleVarianceTwoPass_relError_le_linear_u_add_problem110_remainder`.
  These package the existing explicit two-pass sample-variance remainder as a
  named nonnegative term, giving the source-facing form
  `relError <= (n+3)u + R_110`.  Added the non-vacuity checks
  `flSampleVarianceTwoPassProblem110MeanQuadraticBound_eq_zero_of_u_eq_zero`,
  `flSampleVarianceTwoPassProblem110Remainder_eq_zero_of_u_eq_zero`, and
  `flSampleVarianceTwoPass_relError_eq_zero_of_u_eq_zero`, proving that at
  zero unit roundoff the named remainder and modeled relative error vanish.
  Reran
  `lake build LeanFpAnalysis.FP.Analysis.SampleVariance`; it exited
  successfully.  Reran `lake env lean examples/LibraryLookup.lean`, with
  output redirected to
	  `/private/tmp/librarylookup-ch1-samplevariance-problem110-remainder.out`; it
	  exited successfully and produced 50528 lines.  The focused axiom audit for
	  the three new theorem declarations reports `[propext, Classical.choice,
	  Quot.sound]`.  Reran no-forbidden-token, trailing-whitespace, and diff-check
	  hygiene for the touched SampleVariance/lookup/ledger files; all were clean.
- 2026-06-13 focused Problem 1.10 coefficient-times-`u^2` envelope: added
  `flSampleVarianceTwoPassProblem110RemainderQuadraticCoeff` and
  `flSampleVarianceTwoPassProblem110RemainderQuadraticBound_eq_coeff_mul_u_sq`.
  These prove that the already closed quadratic envelope is exactly a fixed
  data-dependent coefficient times `fp.u^2`, giving a theorem-level coefficient
  form for the source `O(u^2)` reading; the literal Landau wrapper is recorded
  in the subsequent 2026-06-13 checkpoint.
  Reran `lake build LeanFpAnalysis.FP.Analysis.SampleVariance`; it exited
  successfully. Reran `lake env lean examples/LibraryLookup.lean`; after the
  focused build it exited successfully. The focused axiom audit for the new
  coefficient theorem and the quadratic-bound theorem reports `[propext,
  Classical.choice, Quot.sound]`. Reran no-forbidden-token, trailing-whitespace,
  and diff-check hygiene for the touched SampleVariance/lookup/ledger files; all
  were clean.
- 2026-06-13 focused Problem 1.10 quadratic-remainder envelope: added
  `flSampleVarianceTwoPassProblem110RemainderQuadraticBound` and
  `flSampleVarianceTwoPassProblem110Remainder_le_quadratic_bound`. These prove
  that the named higher-order remainder `R_110` is bounded by an explicit
  quadratic expression in `u` under `(n+3)u <= 1/2`, `n > 1`, and positive exact
  variance, closing the theorem-level source `O(u^2)` reading without a
  pointwise or data-path enumeration. Reran
  `lake build LeanFpAnalysis.FP.Analysis.SampleVariance`; it exited
  successfully. Reran `lake env lean examples/LibraryLookup.lean`, with output
  redirected to
  `/private/tmp/librarylookup-ch1-samplevariance-quadratic-bound.out`; it
  exited successfully and produced 50539 lines. The focused axiom audit for
  `flSampleVarianceTwoPassProblem110Remainder_le_quadratic_bound` reports
  `[propext, Classical.choice, Quot.sound]`. Reran no-forbidden-token,
  trailing-whitespace, and diff-check hygiene for the touched
  SampleVariance/lookup/ledger files; all were clean.
- 2026-06-13 focused Problem 1.10 literal Landau wrapper: added
  `flSampleVarianceTwoPassProblem110RemainderQuadraticEnvelope`,
  `flSampleVarianceTwoPassProblem110RemainderQuadraticEnvelope_eq_bound`, and
  `flSampleVarianceTwoPassProblem110RemainderQuadraticEnvelope_isBigO`. These
  prove that the existing FP-model quadratic envelope is the scalar envelope
  evaluated at `fp.u`, and that for fixed data this scalar envelope is
  literally `O(u^2)` as `u -> 0` in mathlib Landau notation. Reran
  `lake build LeanFpAnalysis.FP.Analysis.SampleVariance`; it exited
  successfully. Reran `lake env lean examples/LibraryLookup.lean`, with output
  redirected to `/private/tmp/librarylookup-ch1-samplevariance-bigo.out`; after
  rebuilding the stale `LeanFpAnalysis.FP.Algorithms.CompensatedSum` olean, the
  lookup run exited successfully and produced 55166 lines. The focused axiom
  audit for the two new theorem declarations reports `[propext,
  Classical.choice, Quot.sound]`. Reran no-forbidden-token,
  trailing-whitespace, and diff-check hygiene for the touched
  SampleVariance/lookup/ledger files; all were clean.
- 2026-06-13 focused Problem 1.7 literal Landau wrapper: added
  `sampleVarianceProblem17RelativeRemainderCoeff`,
  `sampleVarianceProblem17RelativeRemainderEnvelope`,
  `sampleVarianceTwoPass_relative_add_scaled_sub_linear_eq_remainder`, and
  `sampleVarianceProblem17RelativeRemainderEnvelope_isBigO`. These prove that
  after dividing the finite-difference sample-variance change by the exact
  variance and subtracting the first-order directional coefficient, the
  relative remainder is an explicit quadratic envelope and is literally
  `O(t^2)` as `t -> 0`. Reran
  `lake build LeanFpAnalysis.FP.Analysis.SampleVariance`; it exited
  successfully. Reran `lake env lean examples/LibraryLookup.lean`, with output
  redirected to `/private/tmp/librarylookup-ch1-samplevariance-p17-bigo.out`;
  it exited successfully. The focused axiom audit for the two new theorem
  declarations reports `[propext, Classical.choice, Quot.sound]`. Reran
  no-forbidden-token, trailing-whitespace, and diff-check hygiene for the
  touched SampleVariance/lookup/ledger files; all were clean.
- 2026-06-12 focused §1.12.1 supplied pivoted primitive bridge: added
  `noPivotPartialPivotRoundedU`, `noPivotPartialPivotPrimitiveRoundedU`,
  `noPivotPartialPivotPrimitiveRoundedU_eq_roundedU_of_rounds`,
  `noPivotPartialPivotRoundedLUBackwardError`, and
  `noPivotPartialPivotPrimitiveRoundedLUBackwardError_of_rounds`.  These prove
  that for every `epsilon >= 0`, if the pivoted primitive operations supply
  `fl(epsilon/1)=epsilon`, `fl(epsilon*1)=epsilon`, and
  `fl((-1)-epsilon)=-1`, then the rounded pivoted factors satisfy the
  componentwise pivoted LU backward-error certificate with radius `epsilon`.
  At this checkpoint, those three supplied primitive threshold theorems
  remained open; the
  2026-06-13 pivoted-threshold update closes that checkpoint gap.  Reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`,
  `lake env lean examples/LibraryLookup.lean`, and the new-theorem
  `#print axioms` audit; the axiom report is
  `[propext, Classical.choice, Quot.sound]`.
- 2026-06-12 focused §1.14.1 local relative-error bridge: added
  `expm1Algorithm2RoundedCore_relError_le_gamma4`,
  `expm1Algorithm2SlowRatioPerturbationBound`,
  `expm1Algorithm2LocalRelErrorBound`, and
  `expm1Algorithm2RoundedCore_relError_le_local_bound`. These expose the
  generic `gamma_4` Algorithm 2 core wrapper as a Chapter 1 `relError`
  theorem and compose the exact slow-ratio drift for `yhat=y*(1+delta)` with
  the local rounded arithmetic factor. Reran
  `lake build LeanFpAnalysis.FP.Analysis.CancellationOfRoundingErrors`,
  `lake env lean examples/LibraryLookup.lean`, and the new-theorem
  `#print axioms` audit; the axiom report is
  `[propext, Classical.choice, Quot.sound]`. Concrete exp/log routine
  contracts, Ferguson-condition verification for the actual rounded `yhat`,
  Table 1.2 machine derivation, and the concrete drift instantiation for the
  roughly `3.5u` bound remain open.
- 2026-06-12 focused §1.14.1 certificate-consumer bridge: added
  `expm1Algorithm2LocalRelErrorBound_eq_drift_div_add_gamma4`,
  `expm1Algorithm2LocalRelErrorBound_le_eta_add_gamma4`, and
  `expm1Algorithm2RoundedCore_relError_le_eta_add_gamma4`. These reduce the
  next local Algorithm 2 instantiation to a normalized drift certificate:
  prove `drift <= eta*|g(y)|`, and the rounded-core relative error follows as
  `eta + (1+eta)*gamma_4`. Reran
  `lake build LeanFpAnalysis.FP.Analysis.CancellationOfRoundingErrors`,
  refreshed stale lookup dependencies
  `LeanFpAnalysis.FP.Algorithms.LeastSquares.LSQRSolve`,
  `LeanFpAnalysis.FP.Algorithms.RandNLA.ElementwiseSpectral`, and
  `LeanFpAnalysis.FP.Algorithms.RandNLA.UniformRowSamplingFP`, reran
  `lake env lean examples/LibraryLookup.lean`, and reran the new-theorem
  `#print axioms` audit; the axiom report is
  `[propext, Classical.choice, Quot.sound]`.
- 2026-06-12 focused §1.14.1 primitive drift-certificate bridge: added
  `expm1Algorithm2PrimitiveDriftBound`,
  `expm1Algorithm2SlowRatioPerturbationBound_le_of_abs_bounds`,
  `expm1Algorithm2LocalDrift_le_primitive_bound`, and
  `expm1Algorithm2RoundedCore_relError_le_eta_add_gamma4_of_primitive_bounds`.
  These turn elementary absolute-value budgets for `|g(y)|`, `|y-1|`,
  `|yhat-1|`, and `|delta|` into the existing normalized local Algorithm 2
  relative-error certificate. This is the compact replacement for a pointwise
  interval/case expansion; concrete exp/log routine contracts, actual-`yhat`
  Ferguson-condition verification, Table 1.2 machine derivation, and the concrete drift
  instantiation for the roughly `3.5u` theorem remain open. Reran
  `lake build LeanFpAnalysis.FP.Analysis.CancellationOfRoundingErrors`,
  rebuilt the missing umbrella dependency
  `LeanFpAnalysis.FP.Algorithms`, reran `lake env lean examples/LibraryLookup.lean`,
  and reran the new-theorem `#print axioms` audit; the axiom report is
  `[propext, Classical.choice, Quot.sound]`.
- 2026-06-12 focused §1.14.1 signed-product gamma3 bridge: added
  `expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma3`,
  `expm1Algorithm2RoundedCore_relError_le_gamma3`,
  `expm1Algorithm2RoundedCore_relError_le_local_bound_gamma3`,
  `expm1Algorithm2RoundedCore_relError_le_eta_add_gamma3`, and
  `expm1Algorithm2RoundedCore_relError_le_eta_add_gamma3_of_primitive_bounds`.
  These reuse `prod_signed_error_bound` to charge the equation (1.9) factors as
  `gamma_3` instead of the conservative `gamma_4`, and carry the same primitive
  drift certificate through to `eta + (1+eta)*gamma_3`. Follow-up corollaries
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_remainder`
  and
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_remainder_of_primitive_bounds`
  now state the explicit source-shaped
  `3.5u + ((3u)^2)/(1-3u) + (u/2)*gamma_3` bound under a `(u/2)*|g(y)|`
  drift hypothesis. Remaining work for the source's roughly `3.5u` sentence is
  to prove that concrete drift instantiation from exp/log and actual-`yhat`
  Ferguson-condition hypotheses. Reran
  `lake build LeanFpAnalysis.FP.Analysis.CancellationOfRoundingErrors`, rebuilt
  the missing lookup dependencies
  `LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation` and
  `LeanFpAnalysis.FP.Algorithms.RandNLA.Preconditioning`, reran
  `lake env lean examples/LibraryLookup.lean`, and reran the new-theorem
  `#print axioms` audit; the axiom report is
  `[propext, Classical.choice, Quot.sound]`.
- 2026-06-12 focused §1.14.1 local-remainder refinement: added
  `expm1Algorithm2PrimitiveSlowRemainderBound`,
  `expm1Algorithm2PrimitiveDriftBound_le_half_u_mul_abs_logRatio_add_slow_remainder`,
  and
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_local_remainder_of_abs_bounds`.
  These prove the leading `0.5u + 3u` contribution from `deltaAbs <= u`
  directly and expose the remaining Algorithm 2 small-neighborhood work as the
  explicit normalized slow-ratio remainder
  `S/|g(y)|*(1+gamma_3)`. The follow-up wrapper
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_normalized_remainder_of_abs_bounds`
  consumes a certificate `S <= rem*|g(y)|` and replaces that term by
  `rem*(1+gamma_3)`. Reran
  `lake build LeanFpAnalysis.FP.Analysis.CancellationOfRoundingErrors`, reran
  `lake env lean examples/LibraryLookup.lean`, and reran the wrapper/local
  theorem `#print axioms` audit; both axiom reports are
  `[propext, Classical.choice, Quot.sound]`. Also repaired the Chapter 1
  lookup row's Markdown-table notation by replacing raw absolute-value pipes
  with `abs(...)` prose inside the table cell.
- 2026-06-12 focused §1.14.1 radius-remainder refinement: added
  `expm1Algorithm2PrimitiveSlowRemainderBound_le_of_radius` and
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_radius_remainder_of_abs_bounds`.
  These compress the explicit slow-ratio remainder into
  `(6*r^2 + (r/2 + 3*r^2)*u/2)/|g(y)|*(1+gamma_3)` under `yAbs <= r` and
  `yhatAbs <= r`, preserving the non-enumerative proof route for later
  interval or machine-specific instantiations. Reran
  `lake build LeanFpAnalysis.FP.Analysis.CancellationOfRoundingErrors`, reran
  `lake env lean examples/LibraryLookup.lean`, and reran the new radius theorem
  `#print axioms` audit; the axiom reports are
  `[propext, Classical.choice, Quot.sound]`.
- 2026-06-12 focused §1.14.1 denominator-radius refinement: added
  `expm1LogRatio_abs_ge_one_sub_radius_bound` and
  `expm1LogRatio_abs_ge_half_of_radius`, turning the existing close-to-one
  estimate for `g(y)` into reusable lower bounds for `|g(y)|` in local radius
  arguments. Reran
  `lake build LeanFpAnalysis.FP.Analysis.CancellationOfRoundingErrors`, reran
  `lake env lean examples/LibraryLookup.lean`, and reran the new denominator
  theorem `#print axioms` audit; the axiom reports are
  `[propext, Classical.choice, Quot.sound]`.
- 2026-06-12 focused §1.14.1 denominator-free radius bound: added
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_radius_bound_of_abs_bounds`.
  This combines the radius-remainder theorem with
  `expm1LogRatio_abs_ge_half_of_radius`, replacing the explicit
  `/|g(y)|` tail by
  `2*(6*r^2 + (r/2 + 3*r^2)*u/2)*(1+gamma_3)` when `r <= 1/3`. Reran
  `lake build LeanFpAnalysis.FP.Analysis.CancellationOfRoundingErrors` and the
  focused theorem `#print axioms` audit; the axiom report is
  `[propext, Classical.choice, Quot.sound]`. At that pass the new `#check` was
  present in `examples/LibraryLookup.lean`; a later 2026-06-13 redirected full
  lookup run is recorded below.
- 2026-06-12 focused §1.14.1 unit-roundoff-radius refinement: added
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_u_radius_bound_of_abs_bounds`.
  This specializes the denominator-free radius theorem to `r = u`, giving the
  explicit tail `((25/2)*u^2 + 3*u^3)*(1+gamma_3)` once `yAbs <= u` and
  `yhatAbs <= u`. Reran
  `lake build LeanFpAnalysis.FP.Analysis.CancellationOfRoundingErrors` and the
  focused theorem `#print axioms` audit; the axiom report is
  `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 focused §1.14.1 direct unit-bound refinement: added
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_u_radius_bound_of_unit_bounds`.
  This is the non-enumerative local endpoint for the current branch: it consumes
  `|y-1| <= u`, `|yhat-1| <= u`, and `|delta| <= u` directly and returns the
  leading `3.5u` theorem plus the explicit
  `((25/2)*u^2 + 3*u^3)*(1+gamma_3)` tail. Reran
  `lake build LeanFpAnalysis.FP.Analysis.CancellationOfRoundingErrors` and the
  focused theorem `#print axioms` audit; the axiom report is
  `[propext, Classical.choice, Quot.sound]`. Reran
  `lake env lean examples/LibraryLookup.lean` with output redirected to
  `/private/tmp/librarylookup-ch1-direct.out`; it exited successfully.
- 2026-06-13 focused §1.14.1 Algorithm 2 named local `3.5u` bound: added
  `expm1Algorithm2ThreePointFiveUnitBound`,
  `expm1Algorithm2Gamma3Scalar`,
  `expm1Algorithm2ThreePointFiveUnitBoundScalar`,
  `expm1Algorithm2ThreePointFiveUnitBound_eq_scalar`,
  `expm1Algorithm2ThreePointFiveUnitBoundScalar_isBigO`,
  `expm1Algorithm2ThreePointFiveUnitBound_eq_zero_of_u_eq_zero`, and
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_unit_bound_of_unit_bounds`.
  These package the detailed unit-bound RHS as one named local bound, expose
  the corresponding scalar envelope as a function of unit roundoff, prove this
  scalar envelope is `O(u)` as `u -> 0`, prove the zero-roundoff sanity case,
  and expose the compact theorem surface consuming
  `|y-1| <= u`, `|yhat-1| <= u`, and `|delta| <= u`. Reran
  `lake build LeanFpAnalysis.FP.Analysis.CancellationOfRoundingErrors`; it
  exited successfully. Reran `lake env lean examples/LibraryLookup.lean` with
  output redirected to
  `/private/tmp/librarylookup-ch1-expm1-named-unit-bound.out`; it exited
  successfully with `50840` output lines. The focused axiom audit for the
  theorem declarations reports `[propext, Classical.choice, Quot.sound]`.
- 2026-06-14 focused §1.14.1 Algorithm 2 named-bound scalar envelope:
  added `expm1Algorithm2Gamma3Scalar`,
  `expm1Algorithm2ThreePointFiveUnitBoundScalar`,
  `expm1Algorithm2ThreePointFiveUnitBound_eq_scalar`, and
  `expm1Algorithm2ThreePointFiveUnitBoundScalar_isBigO`. These expose the
  bulky local `3.5u` unit-radius bound as a scalar function of `u`, prove the
  model-indexed bound is that scalar envelope evaluated at `fp.u`, and prove
  the scalar envelope is `O(u)` as `u -> 0`. This is an interpretation of the
  local bound, not a concrete exp/log routine or Table 1.2 machine trace.
  Reran `lake build LeanFpAnalysis.FP.Analysis.CancellationOfRoundingErrors`;
  it exited successfully. A focused `#check` file importing
  `LeanFpAnalysis.FP.Analysis.CancellationOfRoundingErrors` recognizes all
  four declarations, and the focused axiom audit for the two theorem
  declarations reports `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 focused §1.14.1 source-shaped exp-perturbation radius refinement:
  added `expm1Algorithm2_yhat_sub_one_abs_le_of_y_radius` and
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_perturb_radius_bound`.
  These prove the non-enumerative handoff from the page-23 model
  `yhat=y*(1+delta)`: from `|y-1| <= r` and `|delta| <= u`, Lean derives
  `|yhat-1| <= r + (1+r)u` and feeds that combined radius into the
  denominator-free `3.5u` theorem. Reran
  `lake build LeanFpAnalysis.FP.Analysis.CancellationOfRoundingErrors`; it
  exited successfully. The focused axiom audit for both new theorems reports
  `[propext, Classical.choice, Quot.sound]`. The new `#check`s are present in
  `examples/LibraryLookup.lean`; a full redirected lookup run currently exits
  nonzero because unrelated Chapter 4 insertion-schedule lookup constants at
  lines 2783--2790 are unknown.
- 2026-06-13 focused §1.14.1 small-`x` source-radius refinement: added
  `expm1Algorithm2_exp_sub_one_abs_le_of_abs_x_le`,
  `expm1LogRatio_exp_ne_zero_of_ne_zero`, and
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_x_radius_bound`.
  These instantiate the previous `y`-radius bridge with `y = exp x`:
  `|x| <= X` gives `|exp x - 1| <= exp X - 1`, `x != 0` proves the slow ratio
  denominator/numerator are nonzero, and the Algorithm 2 theorem consumes the
  combined radius `(exp X - 1) + exp X*u`. Reran
  `lake build LeanFpAnalysis.FP.Analysis.CancellationOfRoundingErrors`; it
  exited successfully. The focused axiom audit for all three new declarations
  reports `[propext, Classical.choice, Quot.sound]`. Reran
  `lake env lean examples/LibraryLookup.lean` with output redirected to
  `/private/tmp/librarylookup-ch1-exp-x-radius.out`; it exited successfully.
- 2026-06-13 focused §1.14.1 exp-`x` scalar smallness adapter: added
  `expm1Algorithm2_exp_x_combined_radius_le_third_of_exp_mul_one_add_u_le`
  and
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_x_mul_one_add_u_bound`.
  These close the abstract radius side condition for the small-`x` wrapper:
  the propagated radius `(exp X - 1) + exp X*u` is at most `1/3` whenever
  `exp X*(1+u) <= 4/3`. Reran
  `lake build LeanFpAnalysis.FP.Analysis.CancellationOfRoundingErrors`; it
  exited successfully. The focused axiom audit for both declarations reports
  `[propext, Classical.choice, Quot.sound]`. Reran
  `lake env lean examples/LibraryLookup.lean`; it exited successfully.
- 2026-06-13 focused §1.14.1 guard-digit subtraction adapter: added
  `expm1Algorithm2RoundedCore_eq_source_1_9_of_exact_sub`,
  `expm1Algorithm2RoundedCore_eq_source_1_9_of_guardDigitSubtractionModel`,
  and `expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_ferguson`.
  These refine equation (1.9) with `epsSub = 0` when the `yhat - 1`
  subtraction is exact, when a guard-digit subtraction model plus Ferguson
  condition proves it exact, or when finite round-to-even subtraction is used
  under that Ferguson condition. Reran
  `lake build LeanFpAnalysis.FP.Analysis.CancellationOfRoundingErrors`; it
  exited successfully. The focused axiom audit for all three declarations
  reports `[propext, Classical.choice, Quot.sound]`. Reran
  `lake env lean examples/LibraryLookup.lean`; it exited successfully.
- 2026-06-13 focused §1.14.1 Sterbenz local-radius exact-subtraction adapter:
  added
  `expm1Algorithm2_yhat_one_sterbenzRatioCondition_of_abs_sub_one_le_third`
  and
  `expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_sterbenz_radius`.
  These prove that `|yhat-1| <= 1/3` implies Sterbenz's ratio condition for
  subtracting `1`, and use finite representability plus the finite round-to-even
  operation link to set `epsSub = 0` in equation (1.9). Reran
  `lake build LeanFpAnalysis.FP.Analysis.CancellationOfRoundingErrors`; it
  exited successfully. The focused axiom audit for both declarations reports
  `[propext, Classical.choice, Quot.sound]`. Reran
  `lake env lean examples/LibraryLookup.lean`; it exited successfully.
- 2026-06-13 focused §1.14.1 source-shaped Sterbenz wrappers: added
  `expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_exp_perturb_sterbenz_radius`,
  `expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_exp_x_sterbenz_radius`,
  and
  `expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_exp_x_mul_one_add_u_sterbenz`.
  These derive the `|yhat-1| <= 1/3` Sterbenz exact-subtraction condition from
  `yhat = y*(1+delta)`, then from `y = exp x` and `|x| <= X`, and finally
  from the compact source smallness hypothesis `exp X*(1+u) <= 4/3`; this
  replaces pointwise exponent-case checking for the local Algorithm 2
  subtraction. Reran
  `lake build LeanFpAnalysis.FP.Analysis.CancellationOfRoundingErrors`; it
  exited successfully. The focused axiom audit for all three declarations
  reports `[propext, Classical.choice, Quot.sound]`. Reran
  `lake env lean examples/LibraryLookup.lean` with output redirected to
  `/private/tmp/librarylookup-ch1-sterbenz-wrappers.out`; it exited
  successfully.
- 2026-06-13 focused §1.14.1 exact-subtraction `gamma_2` core: added
  `expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_exact_sub`,
  `expm1Algorithm2RoundedCore_relError_le_gamma2_of_exact_sub`,
  `expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_sterbenz_radius`,
  the source-shaped exact-subtraction wrappers
  `expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_perturb_sterbenz_radius`,
  `expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_x_sterbenz_radius`,
  and
  `expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_x_mul_one_add_u_sterbenz`,
  plus the compact source-domain `gamma_2` wrappers
  `expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_finiteRoundToEven_exp_x_mul_one_add_u_sterbenz`
  and
  `expm1Algorithm2RoundedCore_relError_le_gamma2_of_finiteRoundToEven_exp_x_mul_one_add_u_sterbenz`.
  These expose `fp.fl_sub yhat 1 = yhat - 1` and charge only the rounded log
  plus final division factors on the finite round-to-even/Sterbenz path.
  Reran `lake build LeanFpAnalysis.FP.Analysis.CancellationOfRoundingErrors`;
  it exited successfully. The focused axiom audit for all eight declarations
  reports `[propext, Classical.choice, Quot.sound]`. Reran
  `lake env lean examples/LibraryLookup.lean` with output redirected to
  `/private/tmp/librarylookup-ch1-gamma2.out`; it exited successfully.
- 2026-06-13 focused §1.14.1 rounded-exp finite-output bridge: added
  `FloatingPointFormat.finiteRoundToEven_finiteSystem`,
  `FloatingPointFormat.finiteRoundToEvenOp_finiteSystem`, and
  `FloatingPointFormat.finiteRoundToEvenSqrt_finiteSystem`, plus the
  rounded-exp-produced Algorithm 2 wrappers
  `expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_rounded_exp_x_mul_one_add_u_sterbenz`,
  `expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_finiteRoundToEven_rounded_exp_x_mul_one_add_u_sterbenz`,
  and
  `expm1Algorithm2RoundedCore_relError_le_gamma2_of_finiteRoundToEven_rounded_exp_x_mul_one_add_u_sterbenz`.
  These discharge the `yhat` finite-representability hypothesis from the
  concrete equality `yhat = finiteRoundToEven(exp x)` while preserving the
  explicit subtraction operation-link obligation. Reran
  `lake build LeanFpAnalysis.FP.Analysis.FloatingPointArithmetic` and
  `lake build LeanFpAnalysis.FP.Analysis.CancellationOfRoundingErrors`; both
  exited successfully. The focused axiom audit for all six declarations
  reports `[propext, Classical.choice, Quot.sound]`. Reran
  `lake env lean examples/LibraryLookup.lean` with output redirected to
  `/private/tmp/librarylookup-ch1-rounded-exp-finite.out`; it exited
  successfully.
- 2026-06-13 focused §1.14.1 finite-normal rounded-exp delta bridge: added
  `expm1Algorithm2RoundedExp_delta_abs_le_of_finiteNormalRange`,
  `expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_finiteNormal_sterbenz`,
  `expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_finiteRoundToEven_exp_finiteNormal_sterbenz`,
  and
  `expm1Algorithm2RoundedCore_relError_le_gamma2_of_finiteRoundToEven_exp_finiteNormal_sterbenz`.
  These derive the Algorithm 2 `|delta| <= fp.u` input from the finite-normal
  round-to-even contract for `exp x` and compose it into the exact-subtraction
  and `gamma_2` local core. Reran
  `lake build LeanFpAnalysis.FP.Analysis.CancellationOfRoundingErrors`; it
  exited successfully. Reran `lake env lean examples/LibraryLookup.lean` with
  output redirected to
  `/private/tmp/librarylookup-ch1-finite-normal-rounded-exp.out`; it exited
  successfully. The focused axiom audit for all four declarations reports
  `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 focused §1.14.1 finite-normal rounded-log bridge: added
  `expm1Algorithm2RoundedLog_exists_contract_of_finiteNormalRange`,
  `expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_finiteRoundToEven_exp_log_finiteNormal_sterbenz`,
  and
  `expm1Algorithm2RoundedCore_relError_le_gamma2_of_finiteRoundToEven_exp_log_finiteNormal_sterbenz`.
  These derive the rounded-log `epsLog` witness, `logHat != 0`, and
  `0 < 1+epsLog` from `logHat = finiteRoundToEven(log yhat)` under finite
  normal range, `fmt.unitRoundoff <= fp.u`, and `fmt.unitRoundoff < 1`, then
  compose the rounded-exp and rounded-log contracts into the local `gamma_2`
  core. Reran `lake build LeanFpAnalysis.FP.Analysis.CancellationOfRoundingErrors`;
  it exited successfully. Reran `lake build LeanFpAnalysis.FP.Algorithms.InsertionSum`
  to refresh the imported lookup dependency, then reran
  `lake env lean examples/LibraryLookup.lean` with output redirected to
  `/private/tmp/librarylookup-ch1-finite-normal-rounded-log.out`; it exited
  successfully. The focused axiom audit for all three declarations reports
  `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 focused §1.14.1 routine-level subtraction link: added
  `finiteRoundToEvenSubtractionLink`,
  `finiteRoundToEvenSubtractionLink.sub_one`,
  `expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_finiteNormal_sterbenz_of_subtractionLink`,
  `expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_finiteRoundToEven_exp_log_finiteNormal_sterbenz_of_subtractionLink`,
  and
  `expm1Algorithm2RoundedCore_relError_le_gamma2_of_finiteRoundToEven_exp_log_finiteNormal_sterbenz_of_subtractionLink`.
  These replace the pointwise produced-`yhat` subtraction equality with one
  routine-level finite round-to-even subtraction link. Reran
  `lake build LeanFpAnalysis.FP.Analysis.CancellationOfRoundingErrors`; it
  exited successfully. Reran `lake env lean examples/LibraryLookup.lean` with
  output redirected to `/private/tmp/librarylookup-ch1-subtraction-link.out`;
  it exited successfully. The focused axiom audit for all four declarations
  reports `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 focused §1.14.1 finite-normal `3.5u` bridge: added
  `expm1LogRatio_exp_eq_algorithm1Exact_of_ne_zero`,
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_log_finiteNormal`,
  and
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_log_finiteNormal_algorithm1Exact`.
  These compose the finite-normal rounded-exp and rounded-log adapters into
  the source-shaped `3.5u` Algorithm 2 theorem and rewrite the comparison
  target to `expm1Algorithm1Exact x`. Reran
  `lake build LeanFpAnalysis.FP.Analysis.CancellationOfRoundingErrors`; it
  exited successfully. Reran `lake env lean examples/LibraryLookup.lean` with
  output redirected to `/private/tmp/librarylookup-ch1-finite-normal-3p5.out`;
  it exited successfully. The focused axiom audit for all three declarations
  reports `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 focused §1.6 normwise supremum condition-number surface: added
  `normwiseConditionNumberSupremumVec`,
  `normwiseConditionNumberAttainedVec`,
  `normwiseConditionNumberSupremumVec.bounded`,
  `normwiseConditionNumberSupremumVec.le_of_bound`,
  `normwiseConditionNumberSupremumVec_of_attained_bound`, and
  `normwise_forward_from_backward_vec_of_condition_supremum`.
  These formalize the source-facing least-upper-bound/attained-maximum
  condition-number language and route it into the normwise
  backward-error-to-forward-error principle. Reran
  `lake build LeanFpAnalysis.FP.Analysis.Stability`; it exited successfully.
  Reran `lake build LeanFpAnalysis.FP` to refresh stale lookup dependencies;
  it exited successfully with pre-existing linter warnings in QR modules. Reran
  `lake env lean examples/LibraryLookup.lean` with output redirected to
  `/private/tmp/librarylookup-ch1-supremum-condition.out`; it exited
  successfully. The focused axiom audit for all six declarations reports
  `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 focused §1.14.2 Givens QR schedule count: added
  `givensQRRectangularRotationCount`,
  `givensQRRectangularRotationCount_twice_int`, and
  `givensQRRectangularRotationCount_ten_by_six`. These formalize the
  rectangular Givens zeroing count stated in the source, using a doubled
  integer identity for `p = n*(m-(n+1)/2)` and the concrete Figure 1.5
  `10 x 6` corollary `p = 39`. Reran
  `lake build LeanFpAnalysis.FP.Algorithms.QR.GivensSpec`; it exited
  successfully with pre-existing unused-simp warnings in `GivensSpec`. Reran
  `lake env lean examples/LibraryLookup.lean`; it exited successfully. The
  focused axiom audit for all three declarations reports
  `[propext, Classical.choice, Quot.sound]`.
- 2026-06-14 focused §1.14.2 Givens zeroing algebra: added
  `givensRotation_mulVec_p`, `givensRotation_mulVec_q`,
  `givensRotation_ratio_zeroes_q`, and `givensRotation_ratio_mulVec_p`.
  These prove the two affected-component formulas for an embedded Givens
  rotation and the source ratio choice that zeroes the selected component.
  Reran `lake build LeanFpAnalysis.FP.Algorithms.QR.GivensSpec`; it exited
  successfully with pre-existing unused-simp warnings in `GivensSpec`. Reran
  `lake build LeanFpAnalysis.FP.Analysis.NonrandomRounding` to refresh a stale
  lookup dependency, then reran `lake env lean examples/LibraryLookup.lean`
  with output redirected to `/private/tmp/librarylookup-ch1-givens-zeroing.out`;
  it exited successfully with `58160` output lines. The focused axiom audit for
  all four declarations reports `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 focused §1.16 upper-Hessenberg entrywise nearby-matrix and
  determinant-product bridge: added `hessenbergEntrywisePerturbation`,
  `hessenbergEntrywisePerturbation_diag`,
  `hessenbergEntrywisePerturbation_subdiag`,
  `hessenbergDiagRoundedStep_eq_entrywisePerturbedExactStep`,
  `hessenbergDetRoundedProduct_relError_le_gamma_of_det_eq_diag_prod`,
  `hessenbergDetExampleRoundedProduct_relError_le_gamma`, and
  `hessenbergDetExample_alpha_ten_pow_roundedProduct_relError_le_gamma`,
  closing the displayed entrywise nearby-matrix adapter and the
  determinant-product mixed-stability bridge for any matrix whose exact
  determinant equals the computed diagonal product, for the displayed family,
  and for the `alpha=10^-7` source value. Reran
  `lake build LeanFpAnalysis.FP.Analysis.ProblemDependentStability`; it exited
  successfully. Reran
  `lake env lean examples/LibraryLookup.lean`, with output redirected to
  `/private/tmp/librarylookup-ch1-hessenberg-mixed.out`; it exited
  successfully; after adding the entrywise adapter checks, reran it again with
  output redirected to `/private/tmp/librarylookup-ch1-hessenberg-entrywise.out`,
  and it exited successfully. The focused axiom audits for the six theorem
  declarations report `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 focused §1.16 upper-Hessenberg entrywise perturbation bounds:
  added `hessenbergSubdiagPerturbationFactors`,
  `hessenbergSubdiagPerturbationFactors_prod`,
  `hessenbergEntrywisePerturbation_isUpperHessenberg`,
  `hessenbergEntrywisePerturbation_diag_signedRelErrorWitness`,
  `hessenbergEntrywisePerturbation_diag_abs_error_le`,
  `hessenbergEntrywisePerturbation_subdiag_signedRelErrorWitness_exists`,
  `hessenbergEntrywisePerturbation_subdiag_abs_error_le_gamma`, and
  `hessenbergEntrywisePerturbation_abs_error_le_gamma_three`, closing the
  source's entrywise "differing negligibly from A" claim for the explicit
  nearby matrix under local unit-roundoff bounds and `gammaValid fp 3`. Reran
  `lake build LeanFpAnalysis.FP.Analysis.ProblemDependentStability`; it exited
  successfully. Reran `lake env lean examples/LibraryLookup.lean`, with output
  redirected to `/private/tmp/librarylookup-ch1-entrywise-bounds.out`; it
  exited successfully. The focused axiom audit for the seven new theorem
  declarations reports `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 focused §1.16 all-updated-diagonals trace wrapper: added
  `HessenbergRoundedDiagTraceOnOriginal`,
  `HessenbergExactDiagTraceOnEntrywisePerturbation`, and
  `hessenbergRoundedDiagTraceOnOriginal_exactTraceOnEntrywisePerturbation`.
  This packages every updated diagonal recurrence into one exact trace on the
  single nearby matrix `hessenbergEntrywisePerturbation n A eps1 eps2 eps3`.
  At this pass, the staged determinant assembly and the primitive
  single-precision trace were still open; later §1.16 validation notes close the
  determinant assembly. Reran
  `lake build LeanFpAnalysis.FP.Analysis.ProblemDependentStability`; it exited
  successfully. Reran `lake env lean examples/LibraryLookup.lean`; it exited
  successfully. A focused scratch check of the three new names passed before
  the scratch file was deleted, and the axiom audit for the new theorem reports
  `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 focused §1.16 nearby-determinant bridge: added
  `hessenbergRoundedDiagTraceOnOriginal_nearbyDet_relError_le_gamma`, which
  combines a source-shaped rounded trace, the single nearby matrix
  `hessenbergEntrywisePerturbation n A eps1 eps2 eps3`, and the remaining
  determinant-product certificate `det(A') = prod computedDiag` to return both
  the exact nearby-matrix trace and the final `gamma_n` relative-error bound for
  the rounded determinant product against `det(A')`. This narrows the remaining
  §1.16 theorem obligation to proving that determinant-product certificate from
  the full upper-Hessenberg GE path, plus the separate primitive
  single-precision trace for Table 1.3. Reran
  `lake build LeanFpAnalysis.FP.Analysis.ProblemDependentStability`; it exited
  successfully. Reran `lake env lean examples/LibraryLookup.lean`; it exited
  successfully. The focused scratch axiom audit for the new theorem reports
  `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 focused §1.16 generic 4-by-4 no-pivot endpoint determinant:
  added `hessenberg4NoPivotPivot0`, `hessenberg4NoPivotMultiplier10`,
  `hessenberg4NoPivotDiag1`, `hessenberg4NoPivotSuper12`,
  `hessenberg4NoPivotSuper13`, `hessenberg4NoPivotMultiplier21`,
  `hessenberg4NoPivotDiag2`, `hessenberg4NoPivotSuper23`,
  `hessenberg4NoPivotMultiplier32`, `hessenberg4NoPivotDiag3`,
  `hessenberg4NoPivotDiag`, `hessenberg4NoPivotEndpoint`,
  `hessenberg4NoPivotEndpoint_blockTriangular`, and
  `hessenberg4NoPivotEndpoint_det_eq_diag_prod`. This closes the endpoint
  determinant-product layer for a generic 4-by-4 upper-Hessenberg no-pivot
  symbolic endpoint. At this pass, the local diagonal-recurrence matching and
  determinant-preservation bridges were still open; the following §1.16
  validation note closes the former. Reran
  `lake build LeanFpAnalysis.FP.Analysis.ProblemDependentStability`; it exited
  successfully. Reran `lake env lean examples/LibraryLookup.lean`, with output
  redirected to `/private/tmp/librarylookup-ch1-hessenberg4-endpoint.out`; it
  exited successfully. The focused scratch axiom audit for the two new theorem
  declarations reports `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 focused §1.16 generic 4-by-4 endpoint diagonal recurrence:
  added `hessenberg4NoPivotPrevSuper`, `hessenberg4NoPivotPrevPivot`,
  `hessenberg4NoPivotDiag_exactTraceOnMatrix`, and
  `hessenberg4NoPivotDiag_exactTraceOnEntrywisePerturbation`. This closes the
  local diagonal-recurrence matching layer for the generic endpoint and for the
  nearby matrix `hessenbergEntrywisePerturbation 4 A eps1 eps2 eps3`, while
  leaving the full-path determinant-preservation certificate and primitive
  single-precision Table 1.3 trace open. Reran
  `lake build LeanFpAnalysis.FP.Analysis.ProblemDependentStability`; it exited
  successfully. Reran `lake env lean examples/LibraryLookup.lean`, with output
  redirected to `/private/tmp/librarylookup-ch1-hessenberg4-trace.out`; it
  exited successfully. The focused scratch axiom audit for the two new theorem
  declarations reports `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 focused §1.16 generic 4-by-4 staged determinant preservation:
  added `hessenberg4NoPivotStage1`, `hessenberg4NoPivotStage2`,
  `hessenberg4NoPivotStage3`, their determinant-preservation theorems,
  `hessenberg4NoPivotStage3_eq_endpoint`,
  `hessenberg4NoPivotEndpoint_det_eq_of_upperHessenberg`,
  `hessenberg4NoPivot_det_eq_diag_prod_of_upperHessenberg`,
  `hessenberg4NoPivotEntrywisePerturbation_det_eq_diag_prod_of_upperHessenberg`,
  and `hessenberg4NoPivotRoundedTrace_nearbyDet_relError_le_gamma`. This closes
  the generic 4-by-4 nearby-matrix determinant-product certificate under the
  explicit upper-Hessenberg and nonzero-pivot hypotheses. The remaining §1.16
  implementation-facing gap is the primitive single-precision Table 1.3 GE
  trace. Reran `lake build LeanFpAnalysis.FP.Analysis.ProblemDependentStability`;
  it exited successfully. Reran `lake env lean examples/LibraryLookup.lean`,
  with output redirected to `/private/tmp/librarylookup-ch1-hessenberg4-stage.out`;
  it exited successfully. The focused axiom audit for the new staged
  determinant and nearby bridge theorems reports
  `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 focused §1.17 Kahan exact-reference all-grid variation: added
  `kahanRationalFunctionFirstDiffKernel`,
  `kahanRationalFunctionFirstDiffKernel_abs_lt_one`,
  `kahanRationalFunction_first_diff_num_factor`,
  `kahanRationalFunction_source_interval_variation_from_first_lt`,
  `kahanRationalFunction_grid_variation_from_first_lt`, and
  `kahanRationalFunction_grid_pair_variation_lt_two`, closing the exact
  source-interval/from-first and all-grid pairwise reference-variation bounds
  without checking the 361 source points one by one. Reran
  `lake build LeanFpAnalysis.FP.Analysis.NonrandomRounding`; it exited
  successfully. Reran `lake env lean examples/LibraryLookup.lean`, with output
  redirected to `/private/tmp/librarylookup-ch1-kahan-grid.out`; it exited
  successfully. The focused axiom audit for the five new theorem declarations
  reports `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 focused §1.17 Kahan abstract rounded-Horner trace: added
  `flKahanHornerNumerator`, `flKahanHornerDenominator`,
  `flKahanRationalFunction`, `kahanHornerNumeratorErrorEval`,
  `kahanHornerDenominatorErrorEval`, and the theorem block
  `flKahanHornerNumerator_eq_errorEval`,
  `flKahanHornerDenominator_eq_errorEval`, and
  `flKahanRationalFunction_eq_errorEval`. This closes the displayed Horner
  operation-order trace at the abstract `FPModel` level with eight numerator
  factors, seven denominator factors, and one final rounded-division factor;
  this abstract layer by itself does not instantiate IEEE double precision or
  prove the Figure 1.6 rounded-value pattern. Reran
  `lake build LeanFpAnalysis.FP.Analysis.NonrandomRounding`; it exited
  successfully. Reran `lake env lean examples/LibraryLookup.lean`, with output
  redirected to `/private/tmp/librarylookup-ch1-kahan-rounded-horner.out`; it
  exited successfully. The focused axiom audit for the three new theorem
  declarations reports `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 focused §1.17 Kahan IEEE-double Horner adapter: added
  `kahanIeeeDoubleUnitRoundoff`, the `ieeeDoubleKahanNumerator_*` and
  `ieeeDoubleKahanDenominator_*` finite round-to-even intermediates,
  `ieeeDoubleKahanHornerNumerator`, `ieeeDoubleKahanHornerDenominator`,
  `ieeeDoubleKahanRationalFunction`,
  `IeeeDoubleKahanNumeratorNormalTrace`,
  `IeeeDoubleKahanDenominatorNormalTrace`,
  `IeeeDoubleKahanQuotientNormalTrace`, and the theorem block
  `ieeeDoubleKahanHornerNumerator_eq_errorEval_of_finiteNormal`,
  `ieeeDoubleKahanHornerDenominator_eq_errorEval_of_finiteNormal`, and
  `ieeeDoubleKahanRationalFunction_eq_errorEval_of_finiteNormal`. This closes
  the displayed Horner operation order for IEEE double finite round-to-even
  arithmetic under explicit finite-normal primitive-result certificates, giving
  strict IEEE-double unit-roundoff local-error factors; at this stage it did not
  prove the source-grid normal certificates or the Figure 1.6 rounded-value
  pattern. Reran `lake build LeanFpAnalysis.FP.Analysis.NonrandomRounding`; it
  exited successfully. Reran `lake env lean examples/LibraryLookup.lean`, with
  output redirected to `/private/tmp/librarylookup-ch1-kahan-ieee-double.out`;
  it exited successfully. The focused axiom audit for the three new theorem
  declarations reports `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 focused §1.17 Kahan source-grid IEEE-double normal certificates:
  added the source-interval and source-grid certificate theorems
  `ieeeDoubleKahanNumeratorNormalTrace_of_source_interval`,
  `ieeeDoubleKahanDenominatorNormalTrace_of_source_interval`,
  `ieeeDoubleKahanNumeratorNormalTrace_of_source_grid`, and
  `ieeeDoubleKahanDenominatorNormalTrace_of_source_grid`, plus the direct
  source-interval/grid local-error corollaries
  `ieeeDoubleKahanHornerNumerator_eq_errorEval_on_source_interval`,
  `ieeeDoubleKahanHornerDenominator_eq_errorEval_on_source_interval`,
  `ieeeDoubleKahanHornerNumerator_grid_eq_errorEval`, and
  `ieeeDoubleKahanHornerDenominator_grid_eq_errorEval`. This closes all
  numerator and denominator finite-normal primitive-result obligations for the
  full source interval and all 361 source grid points by interval certificates,
  not point enumeration. At this stage, the final quotient-division
  finite-normal certificate and the exact continued-fraction reference layer
  remained open; later selected-pair/classification addenda close the
  theorem-level Figure 1.6 nonrandomness claim and treat full plot reproduction
  as optional artifact work. Reran
  `lake build LeanFpAnalysis.FP.Analysis.NonrandomRounding`;
  it exited successfully. Reran `lake env lean examples/LibraryLookup.lean`,
  with output redirected to
  `/private/tmp/librarylookup-ch1-kahan-grid-normal.out`; it exited
  successfully. The focused axiom audit for all eight new theorem declarations
  reports `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 focused §1.17 Kahan IEEE-double quotient certificate: added
  `kahanHornerNumeratorErrorEval_source_interval_bounds`,
  `kahanHornerDenominatorErrorEval_source_interval_bounds`,
  `ieeeDoubleKahanHornerNumerator_source_interval_bounds`,
  `ieeeDoubleKahanHornerDenominator_source_interval_bounds`,
  `ieeeDoubleKahanQuotientNormalTrace_of_source_interval`,
  `ieeeDoubleKahanRationalFunction_eq_errorEval_on_source_interval`,
  `ieeeDoubleKahanQuotientNormalTrace_of_source_grid`, and
  `ieeeDoubleKahanRationalFunction_grid_eq_errorEval`. This closes the final
  quotient-division finite-normal certificate and the full IEEE-double local
  error expansion on all 361 source grid points by interval bounds, not point
  enumeration. At this stage, the exact continued-fraction reference layer
  remained open; later selected-pair/classification addenda close the
  theorem-level Figure 1.6 nonrandomness claim and treat full plot reproduction
  as optional artifact work. Reran
  `lake build LeanFpAnalysis.FP.Analysis.NonrandomRounding`; it exited
  successfully. Reran `lake env lean examples/LibraryLookup.lean`, with output
  redirected to `/private/tmp/librarylookup-ch1-kahan-quotient.out`; it exited
  successfully. The focused axiom audit for these eight theorem declarations
  reports `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 focused §1.17 Kahan continued-fraction reference layer: added
  `kahanContinuedFractionTail1`, `kahanContinuedFractionTail2`,
  `kahanContinuedFractionTail3`, `kahanContinuedFraction`,
  `kahanContinuedFractionP2`, `kahanContinuedFractionP1`,
  `kahanContinuedFraction_eq_rationalFunction`,
  `kahanContinuedFractionP2_neg_on_source_interval`,
  `kahanContinuedFractionP1_neg_on_source_interval`,
  `kahanContinuedFraction_eq_rationalFunction_on_source_interval`,
  `kahanContinuedFraction_grid_eq_rationalFunction`, and
  `kahanContinuedFraction_grid_variation_from_first_lt`. This closes the exact
  continued-fraction reference expression and all-grid continued-fraction
  reference constancy by Euclidean identities and interval denominator
  certificates, not point enumeration. Later selected-pair/classification
  addenda close the theorem-level Figure 1.6 nonrandomness claim and treat full
  plot reproduction as optional artifact work. Reran
  `lake build LeanFpAnalysis.FP.Analysis.NonrandomRounding`;
  it exited successfully. Reran `lake env lean examples/LibraryLookup.lean`,
  with output redirected to
  `/private/tmp/librarylookup-ch1-kahan-continued-fraction.out`; it exited
  successfully. The focused axiom audit for the six new theorem declarations
  reports `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 focused §1.17 Figure 1.6 diagnostic bridge: added
  `kahanRoundedGrid_error_spread_gt_of_output_spread` and
  `ieeeDoubleKahanRationalFunction_grid_error_spread_gt_of_output_spread`.
  These prove that because any two exact source-grid reference values differ by
  less than `2*10^-12`, any supplied rounded-output spread exceeding that
  amount by `η` forces the corresponding rounded-error values to differ by
  more than `η`; the IEEE-double specialization applies this bridge to the
  modeled finite round-to-even Horner path. This reduces the remaining
  Figure 1.6 obligation to certifying enough actual rounded-output entries or
  an equivalent spread certificate, without enumerating all 361 grid points.
  Reran `lake build LeanFpAnalysis.FP.Analysis.NonrandomRounding`; it exited
  successfully. Reran `lake env lean examples/LibraryLookup.lean`, with output
  redirected to `/private/tmp/librarylookup-ch1-kahan-figure16-bridge.out`; it
  exited successfully and produced 50507 lines. The focused axiom audit for the
  two new theorem declarations reports `[propext, Classical.choice,
  Quot.sound]`. Reran no-forbidden-token, trailing-whitespace, and diff-check
  hygiene for the touched NonrandomRounding/lookup/ledger files; all were
  clean.
- 2026-06-13 focused §1.17 Figure 1.6 endpoint diagnostic bridge: added
  `kahanRoundedGrid_endpoint_error_spread_gt_of_output_spread` and
  `ieeeDoubleKahanRationalFunction_endpoint_error_spread_gt_of_output_spread`.
  These reuse `kahanRationalFunction_first_to_last_variation_lt`, so an
  endpoint rounded-output spread above `10^-12 + η` is enough to force
  endpoint rounded-error spread above `η`. This sharpens the remaining
  certificate for the plotted IEEE-double values without enumerating the 361
  grid points. Reran `lake build LeanFpAnalysis.FP.Analysis.NonrandomRounding`;
  it exited successfully. Reran `lake env lean examples/LibraryLookup.lean`,
  with output redirected to
  `/private/tmp/librarylookup-ch1-kahan-endpoint-bridge.out`; it exited
  successfully with `50881` output lines. The focused axiom audit for the two
  theorem declarations reports `[propext, Classical.choice, Quot.sound]`.
  Reran no-forbidden-token, trailing-whitespace, and diff-check hygiene for
  the touched NonrandomRounding/lookup/ledger files; all were clean.
- 2026-06-13 focused Problem 1.8 hidden-mode source-index witness: added
  `mullerModeRatio_lt_100_of_nonneg`,
  `mullerModeY_dominates_of_one_le_of_two_le`,
  `mullerModeRatio_gt_99_of_one_le_of_two_le`,
  `mullerModeRatio_one_34_gt_99`, `mullerModeRatio_one_34_lt_100`, and
  `mullerModeRatio_one_34_within_one_of_hundred`. These prove that
  nonnegative hidden-mode contamination keeps the three-mode ratio below
  `100`, that every unit-or-larger `100^k` contaminant dominates from
  `k >= 2`, and that specializing at source index `k = 34` already puts the
  ratio within one unit of the spurious root. Reran
  `lake build LeanFpAnalysis.FP.Analysis.MullerRecurrence`; it exited
  successfully. Reran `lake env lean examples/LibraryLookup.lean`, with output
  redirected to `/private/tmp/librarylookup-ch1-muller-hidden.out`; it exited
  successfully with `55938` output lines. The focused axiom audit for the six
  new theorem declarations reports `[propext, Classical.choice, Quot.sound]`.
  The focused Lean placeholder scan on
  `LeanFpAnalysis/FP/Analysis/MullerRecurrence.lean` and
  `examples/LibraryLookup.lean` returned no matches, and `git diff --check --`
  for the touched Lean/docs surfaces succeeded.
- 2026-06-13 focused §1.17 selected-pair nonconstancy corollary: added
  `ieeeDoubleKahanStoredGridError`,
  `exists_ieeeDoubleKahanStoredGridError_pair_spread_gt_one_e13`, and
  `not_forall_ieeeDoubleKahanStoredGridError_eq_on_source_grid`. These name the
  stored-input IEEE-double grid-error sequence, preserve the certified
  selected-pair `> 10^-13` spread in that notation, and prove the sequence is
  not constant on the valid source grid. This is a structural corollary of the
  already-certified selected pair, not a 361-point enumeration or full visual
  plot proof. Reran `lake build LeanFpAnalysis.FP.Analysis.NonrandomRounding`;
  it exited successfully. Reran `lake env lean examples/LibraryLookup.lean`,
  with output redirected to
  `/private/tmp/librarylookup-ch1-kahan-error-nonconstant.out`; it exited
  successfully with `55820` output lines. The focused axiom audit for the new
  definition and two theorem declarations reports `[propext, Classical.choice,
  Quot.sound]`. Reran no-forbidden-token, trailing-whitespace, and diff-check
  hygiene for the touched NonrandomRounding/lookup/ledger files; all were
  clean.
- 2026-06-13 focused §1.17 Figure 1.6 selected-pair diagnostic: added
  `kahanRationalFunction_grid_175_289_variation_lt_one_e15`,
  `kahanRoundedGrid_175_289_error_spread_gt_of_output_spread`,
  `ieeeDoubleKahanRationalFunction_175_289_error_spread_gt_of_output_spread`,
  `ieeeDoubleKahanStoredGridPoint`,
  `ieeeDoubleKahanStoredGridRationalFunction`,
  `ieeeDoubleKahanStoredGridPoint_175_eq`,
  `ieeeDoubleKahanStoredGridPoint_289_eq`,
  `ieeeDoubleKahanStoredGridNumerator_m0_175_eq`,
  `ieeeDoubleKahanStoredGridNumerator_m0_289_eq`,
  `ieeeDoubleKahanStoredGridNumerator_s0_175_eq`,
  `ieeeDoubleKahanStoredGridNumerator_s0_289_eq`,
  `ieeeDoubleKahanStoredGridNumerator_m1_175_eq`,
  `ieeeDoubleKahanStoredGridNumerator_m1_289_eq`,
  `ieeeDoubleKahanStoredGridNumerator_s1_175_eq`,
  `ieeeDoubleKahanStoredGridNumerator_s1_289_eq`,
  `ieeeDoubleKahanStoredGridNumerator_m2_175_eq`,
  `ieeeDoubleKahanStoredGridNumerator_m2_289_eq`,
  `ieeeDoubleKahanStoredGridNumerator_s2_175_eq`,
  `ieeeDoubleKahanStoredGridNumerator_s2_289_eq`,
  `ieeeDoubleKahanStoredGridNumerator_m3_175_eq`,
  `ieeeDoubleKahanStoredGridNumerator_m3_289_eq`,
  `ieeeDoubleKahanStoredGridHornerNumerator_175_eq`,
  `ieeeDoubleKahanStoredGridHornerNumerator_289_eq`,
  `ieeeDoubleKahanStoredGridDenominator_s0_175_eq`,
  `ieeeDoubleKahanStoredGridDenominator_s0_289_eq`,
  `ieeeDoubleKahanStoredGridDenominator_m1_175_eq`,
  `ieeeDoubleKahanStoredGridDenominator_m1_289_eq`,
  `ieeeDoubleKahanStoredGridDenominator_s1_175_eq`,
  `ieeeDoubleKahanStoredGridDenominator_s1_289_eq`,
  `ieeeDoubleKahanStoredGridDenominator_m2_175_eq`,
  `ieeeDoubleKahanStoredGridDenominator_m2_289_eq`,
  `ieeeDoubleKahanStoredGridDenominator_s2_175_eq`,
  `ieeeDoubleKahanStoredGridDenominator_s2_289_eq`,
  `ieeeDoubleKahanStoredGridDenominator_m3_175_eq`,
  `ieeeDoubleKahanStoredGridDenominator_m3_289_eq`,
  `ieeeDoubleKahanStoredGridHornerDenominator_175_eq`,
  `ieeeDoubleKahanStoredGridHornerDenominator_289_eq`,
  `ieeeDoubleKahanStoredGridRationalFunction_175_eq`,
  `ieeeDoubleKahanStoredGridRationalFunction_289_eq`,
  `ieeeDoubleKahanStoredGridRationalFunction_175_289_error_spread_gt_of_output_spread`,
  `ieeeDoubleKahanStoredGridRationalFunction_175_289_error_spread_gt_one_e13`,
  and
  `exists_ieeeDoubleKahanStoredGridRationalFunction_grid_error_spread_gt_one_e13`.
  These prove the exact reference spread at grid points `175` and `289` is
  below `10^-15`, turn a supplied rounded-output spread at those two points
  into rounded-error spread, and make the IEEE-double input-storage step
  explicit for the observed high-spread pair. The new stored-grid input
  equalities prove the exact source-grid inputs at `k=175` and `k=289` round to
  `7232781001557191/4503599627370496` and
  `7232781001557305/4503599627370496`, respectively. The new first-operation
  equalities prove `fl(4*xstored)` is exactly representable at both selected
  inputs, giving `7232781001557191/1125899906842624` and
  `7232781001557305/1125899906842624`. The new second-operation equalities
  prove `fl(59-m0)` at the two selected stored inputs, giving
  `7399414187769703/140737488355328` and
  `7399414187769689/140737488355328`; the `k=175` adjacent-bracket certificate
  rounds left and the `k=289` certificate rounds right. The new third-operation
  equalities prove `fl(xstored*s0)` at the two selected stored inputs, giving
  `5941729592779215/70368744177664` and
  `5941729592779297/70368744177664`; the `k=175` certificate rounds right and
  the `k=289` certificate rounds left. The new fourth-operation equalities
  prove `fl(324-m1)` at the two selected stored inputs, giving
  `8428871760391960/35184372088832` and
  `8428871760391920/35184372088832`; both exact subtractions are midpoint
  cases, with tie-to-even choosing the left endpoint at `k=175` and the right
  endpoint at `k=289`. The remaining numerator primitive equalities close
  `fl(xstored*s1)`, `fl(751-m2)`, `fl(xstored*s2)`, and the final rounded
  numerator subtraction at both selected inputs; the final rounded numerator
  values are `4754586561868144/140737488355328` and
  `4754586561867808/140737488355328`. The new denominator and quotient
  equalities close the two selected stored-input denominator traces and final
  divisions; the final rounded outputs are
  `4927149988474991/562949953421312` and
  `2463574994237539/281474976710656`. The unconditional selected-pair theorem
  proves rounded-error spread greater than `10^-13`, and the source-grid
  existential wrapper packages `k=175` and `k=289` as valid grid indices, so
  this selected-pair Figure 1.6 diagnostic is no longer conditional on supplied
  outputs and still uses no 361-point enumeration. Reran
  `lake build LeanFpAnalysis.FP.Analysis.NonrandomRounding`; it exited
  successfully. Reran `lake env lean examples/LibraryLookup.lean`, with output
  redirected to `/private/tmp/librarylookup-ch1-kahan-stored-selected-pair.out`; it
  exited successfully with `51186` output lines. The focused axiom audit for
  the forty-one theorem declarations reports `[propext, Classical.choice,
  Quot.sound]`. Reran no-forbidden-token, trailing-whitespace, and diff-check
  hygiene for the touched NonrandomRounding/lookup/ledger files; all were
  clean.
- 2026-06-13 focused §1.15 perturbed first-step norm bridge: added
  `vecNorm2_pos_of_exists_ne` and
  `beneficialPowerFirstStep_perturbed_vecNorm2_pos_of_delta_row_sum_ne_zero`.
  The new result lifts the existing component-level perturbation theorem to a
  positive Euclidean-norm conclusion whenever some stored perturbation row sum
  is nonzero, without enumerating concrete cases or claiming the hidden
  IEEE/MATLAB perturbation trace. Reran
  `lake build LeanFpAnalysis.FP.Analysis.BeneficialRounding`; it exited
  successfully. Reran `lake env lean examples/LibraryLookup.lean`, with output
  redirected to `/private/tmp/librarylookup-ch1-beneficial-norm.out`; it exited
  successfully with `55746` output lines. The focused axiom audit for the two
  theorem declarations reports `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 focused §1.15 beneficial-rounding binary/IEEE-double exact-storage
  obstruction: added `BinaryTerminating`, `MatrixEntriesBinaryTerminating`,
  `MatrixEntriesFiniteSystem`, `five_not_dvd_two_pow_nat`,
  `one_fifth_not_binaryTerminating`,
  `ieeeDoubleFormat_normalizedSystem_binaryTerminating`,
  `ieeeDoubleFormat_subnormalSystem_binaryTerminating`,
  `ieeeDoubleFormat_finiteSystem_binaryTerminating`,
  `one_fifth_not_ieeeDoubleFiniteSystem`,
  `beneficialPowerMatrix_entry_zero_two_eq_one_fifth`,
  `beneficialPowerMatrix_entry_zero_two_not_binaryTerminating`,
  `beneficialPowerMatrix_entry_zero_two_not_ieeeDoubleFiniteSystem`,
  `beneficialPowerMatrix_not_matrixEntriesBinaryTerminating`, and
  `beneficialPowerMatrix_not_matrixEntriesIeeeDoubleFiniteSystem`. This closes
  the source statement that the displayed matrix is not exactly storable
  entrywise in binary, first by witnessing the `(1,3)` entry `1/5` and proving
  that `1/5 = z/2^n` would force `5 ∣ 2^n`, then by proving every exact
  IEEE-double finite value is terminating binary via the `2^1074` denominator.
  The actual rounded IEEE-double entries, concrete perturbation size, and MATLAB
  iteration trace remain open. Reran
  `lake build LeanFpAnalysis.FP.Analysis.BeneficialRounding`; it exited
  successfully. Reran `lake env lean examples/LibraryLookup.lean`, with output
  redirected to `/private/tmp/librarylookup-ch1-beneficial-binary.out`; it
  exited successfully. The focused axiom audit for the eleven new theorem
  declarations reports `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 focused §1.15 inverse-iteration shifted-system substrate: added
  `inverseIterationShiftedMatrix`, `SolvesInverseIterationShiftedSystem`,
  `inverseIterationShiftedMatrix_mulVec`,
  `inverseIteration_shiftedMatrix_mul_eigenvector`,
  `inverseIteration_shiftedSystem_solution_on_eigenvector`,
  `inverseIteration_shiftedInverse_mul_eigenvector_of_leftInverse`,
  `inverseIteration_shiftedInverse_amplification_abs_eq`, and
  `inverseIteration_shiftedInverse_amplification_strict_of_abs_shift_lt`.
  This closes the exact source statement that inverse iteration is the power
  method applied through the shifted inverse at the algebraic eigenvector layer:
  `(A-mu I)x=(lambda-mu)x`, the shifted solve with eigenvector right-hand side
  returns `(lambda-mu)^{-1}x`, any left inverse has that action, and smaller
  `|lambda-mu|` gives larger scalar amplification. Full-text search of
  `References/Chapter01_full.pdf` found no occurrence of the earlier QR phrase,
  so the §1.15 ledger row was corrected to power method plus inverse iteration.
  The cited inverse-iteration perturbation theorem that the solve error lies almost
  entirely in the required eigenvector direction remains open, as do concrete
  shifted-solve floating-point traces. Reran
  `lake build LeanFpAnalysis.FP.Analysis.BeneficialRounding`; it exited
  successfully. Reran `lake env lean examples/LibraryLookup.lean`, with output
  redirected to `/private/tmp/librarylookup-ch1-beneficial-inverse-iteration.out`;
  it exited successfully. The focused axiom audit for the six new theorem
  declarations reports `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 focused §1.15 inverse-iteration harmless-direction substrate:
  added `matMulVec_smul_right`, `isRightEigenpair_smul`, and
  `inverseIteration_parallel_error_output_isRightEigenpair`. This closes the
  exact algebraic implication that, once the shifted-solve error is supplied as
  parallel to the required eigenvector, the returned inverse-iteration vector is
  still a nonzero scalar multiple of that eigenvector and hence remains the same
  right-eigenpair direction. The theorem deliberately does not prove the
  Parlett/Golub--Van Loan perturbation result that a floating-point shifted
  solve actually produces a near-parallel error; that remains the open
  foundation for the source's full inverse-iteration sentence. Reran
  `lake build LeanFpAnalysis.FP.Analysis.BeneficialRounding`; it exited
  successfully. Reran `lake env lean examples/LibraryLookup.lean`, with output
  redirected to
  `/private/tmp/librarylookup-ch1-beneficial-harmless-direction.out`; it exited
  successfully. The focused axiom audit for the three new theorem declarations
  reports `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 focused §1.15 inverse-iteration near-parallel residual bridge:
  added `eigenResidualVec`, `eigenResidualVec_add_parallel_eq`,
  `eigenResidualVec_norm_le_opNorm_add_abs`,
  `inverseIteration_near_parallel_error_eigenResidual_eq`, and
  `inverseIteration_near_parallel_error_eigenResidual_norm_le`. This closes the
  exact algebraic bridge from a supplied near-parallel shifted-solve error
  `eta*x + r` to the returned vector's eigen-residual: the parallel component
  cancels exactly, and the residual norm is bounded by
  `(A_norm + |lambda|)*||r||_2` under `opNorm2Le A A_norm`. This is a single
  reusable theorem/certificate route, not a finite case enumeration. The cited
  perturbation theorem and concrete floating-point shifted-solve trace supplying
  the near-parallel decomposition remain open. Reran
  `lake build LeanFpAnalysis.FP.Analysis.BeneficialRounding`; it exited
  successfully. Reran `lake env lean examples/LibraryLookup.lean`, with output
  redirected to `/private/tmp/librarylookup-ch1-beneficial-near-parallel.out`;
  it exited successfully with `50582` output lines. The focused axiom audit for
  the four new theorem declarations reports
  `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 focused §1.15 displayed inverse-iteration shifted-solve instance:
  added `beneficialPowerShiftedMatrix_mul_start`,
  `beneficialPower_inverseIteration_shiftedSystem_solution_start`, and
  `beneficialPower_shiftedInverse_mul_start_of_leftInverse`. These specialize
  the generic inverse-iteration substrate to the displayed matrix and start
  vector, proving `(A-mu I)[1,1,1]^T=-mu[1,1,1]^T`, the exact shifted solve
  returns `(-mu)^{-1}[1,1,1]^T` for `mu != 0`, and any left inverse of the
  displayed shifted matrix has that action. This closes an exact §1.15 instance
  layer; the rounded shifted-solve trace and cited near-parallel perturbation
  theorem remain open.
- 2026-06-13 focused §1.12.3 reverse inverse-square exact-prefix transfer:
  added
  `inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixWindow_of_eq_exact`,
  `inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow_of_eq_exact`,
  `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_eq_exact`,
  and
  `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_eq_exact_tight`.
  These theorems compose the exact high-prefix telescoping window with the
  rounded reverse accumulator route: once the rounded high-index prefix is
  proved equal to the exact high-index prefix, the final `10^9` reverse value
  follows from the ordinary or tight suffix-window certificate. This narrows the
  open reverse-order gap to the rounded high-prefix equality or a whole-window
  suffix map; it does not claim the printed reverse value is fully closed.
  Reran `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`;
  it exited successfully. Reran `lake env lean examples/LibraryLookup.lean`,
  with output redirected to
  `/private/tmp/librarylookup-ch1-reverse-exact-prefix-transfer.out`; it exited
  successfully with `50774` output lines. The focused axiom audit for the four
  new theorem declarations reports `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 focused §1.12.3 reverse high-prefix error-margin transfer:
  added `inverseSquareSingleReverseHighPrefixTightWindowMargin`,
  `inverseSquareSingleReverseHighPrefixTightWindowMargin_nonneg`,
  `inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow_of_abs_error_le_margin`,
  and
  `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_abs_error_le_margin`.
  These theorems replace the too-strong exact high-prefix equality target by an
  explicit absolute-error certificate around the exact high-prefix mass; with
  that error certificate and the tight suffix-window map, the source's printed
  reverse value follows. Reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`,
  `lake env lean examples/LibraryLookup.lean`, no-forbidden-token and
  trailing-whitespace scans, and `git diff --check` for the touched Chapter 1
  files/docs; all exited successfully. The focused axiom audit for the new
  reverse margin/transfer declarations reports
  `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 focused §1.12.3 reverse high-prefix rational margin lower bound:
  added `inverseSquareSingleReverseHighPrefixTightWindowMarginLowerBound`,
  `inverseSquareSingleReverseHighPrefixTightWindowMarginLowerBound_nonneg`,
  `inverseSquareSingleReverseHighPrefixTightWindowMarginLowerBound_le_margin`,
  `inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow_of_abs_error_le_marginLowerBound`,
  and
  `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_abs_error_le_marginLowerBound`.
  These theorems use the already-proved telescoping lower and upper bounds to
  put a fully explicit rational slack below the exact refined high-prefix
  margin, so the remaining rounded high-prefix obligation can target that
  concrete absolute-error radius instead of an opaque margin. Reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`;
  it exited successfully. Reran `lake build
  LeanFpAnalysis.FP.Algorithms.PairwiseSum` to restore the missing lookup
  dependency cache, then reran `lake env lean examples/LibraryLookup.lean`; it
  exited successfully. Reran no-forbidden-token and trailing-whitespace scans,
  and `git diff --check` for the touched Chapter 1 files/docs; all exited
  successfully. The focused axiom audit for the new lower-bound declarations
  reports `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 focused §1.12.3 reverse high-prefix shifted margin bound:
  added `inverseSquareTerm_ge_shifted_telescope_4096_8193`,
  `inverseSquareExactReverseAccumulatorFrom_ge_shifted_telescope_4096_8193`,
  `inverseSquareExactReverseTenPowNineHighPrefix_ge_shifted_telescope_4096_8193`,
  `inverseSquareTerm_le_half_telescope`,
  `inverseSquareExactReverseAccumulatorFrom_le_half_telescope`,
  `inverseSquareExactReverseTenPowNineHighPrefix_le_half_telescope`,
  `inverseSquareSingleReverseHighPrefixShiftedLowerEndpoint`,
  `inverseSquareSingleReverseHighPrefixHalfUpperEndpoint`,
  `inverseSquareSingleReverseHighPrefixTightWindowMarginShiftedLowerBound`,
  `inverseSquareSingleReverseHighPrefixTightWindowMarginShiftedLowerBound_nonneg`,
  `inverseSquareSingleReverseHighPrefixTightWindowMarginShiftedLowerBound_le_margin`,
  `inverseSquareSingleReverseTenPowNineHighPrefixCandidate_abs_error_le_shiftedMarginLowerBound`,
  `inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow_of_abs_error_le_shiftedMarginLowerBound`,
  and
  `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_abs_error_le_shiftedMarginLowerBound`.
  The near-half shifted lower telescope and half-shifted upper telescope give a
  much tighter symbolic squeeze on the exact `10^9, ..., 4097` high-prefix
  mass; the resulting explicit rational slack is below the exact refined
  margin and is large enough to contain the concrete high-prefix candidate.
  This replaces the overly conservative coarse telescoping slack as the
  intended rounded-prefix error target, without enumerating suffix cases.
  Reran `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`;
  it exited successfully. Reran `lake env lean examples/LibraryLookup.lean`,
  with output redirected to
  `/private/tmp/librarylookup-ch1-reverse-shifted-margin.out`; it exited
  successfully with `51685` output lines. Reran no-forbidden-token and
  trailing-whitespace scans, and `git diff --check` for the touched Chapter 1
  files/docs; all exited successfully. The focused axiom audit for the shifted
  telescope/margin declarations reports
  `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 focused §1.12.3 reverse high-prefix candidate-window bridge:
  added `inverseSquareSingleReverseHighPrefixCandidateWindowLower`,
  `inverseSquareSingleReverseHighPrefixCandidateWindowUpper`,
  `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow`,
  `inverseSquareSingleReverseHighPrefixCandidateWindow_abs_error_le_shiftedMarginLowerBound`,
  `inverseSquareSingleReverseTenPowNineHighPrefix_abs_error_le_shiftedMarginLowerBound_of_mem_candidateWindow`,
  `inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow_of_mem_candidateWindow`,
  and
  `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_mem_candidateWindow`.
  These theorems package the rounded high-prefix side as a concrete 1024-ulp
  binary32 window around the observed high-prefix candidate: any state in that
  window satisfies the shifted high-prefix error bound, lands in the refined
  suffix-start window, and composes with the tight suffix-window map to give
  Higham's printed reverse value. The remaining work is therefore a candidate
  window-membership proof for the high-prefix trace plus the tight suffix-window
  map, or the older direct candidate equality route. Reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`;
  it exited successfully. Reran `lake env lean examples/LibraryLookup.lean`,
  with output redirected to
  `/private/tmp/librarylookup-ch1-reverse-candidate-window.out`; it exited
  successfully with `51739` output lines. Reran no-forbidden-token and
  trailing-whitespace scans, and `git diff --check` for the touched Chapter 1
  files/docs; all exited successfully. The focused axiom audit for the new
  candidate-window declarations reports
  `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 focused §1.12.3 reverse candidate-window suffix reduction:
  added `inverseSquareSingleReverseTenPowNineHighPrefixCandidate_mem_candidateWindow`,
  `inverseSquareExactReverseTenPowNineHighPrefix_mem_candidateWindow`,
  `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_eq_exact`,
  `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_eq_candidate`,
  `inverseSquareSingleReverseHighPrefixCandidateWindow_mem_printedSuffixStartTightWindow`,
  `inverseSquareSingleReverseCandidateWindowMapsToPrinted`,
  `inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_tightSuffixWindow`,
  `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_candidateWindow_certificates`,
  `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_eq_exact_candidateWindow`,
  and
  `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_eq_candidateWindow`.
  These theorems prove that the observed candidate and exact high-prefix mass
  both lie in the 1024-ulp candidate window, that the candidate window is a
  subwindow of the refined suffix-start window, and that the final reverse
  printed value follows from rounded high-prefix membership plus a suffix map
  on this narrower candidate window. The remaining work is therefore candidate
  window-membership for the rounded high-prefix trace plus a candidate-window
  suffix map, or the older direct candidate equality route. Reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`;
  it exited successfully. Reran `lake env lean examples/LibraryLookup.lean`;
  it exited successfully with `51791` output lines. Reran source placeholder
  scans for `sorry`/`admit`/`axiom`/`unsafe`/`opaque` on the touched Lean
  files and `git diff --check` for the touched Chapter 1 files/docs; all
  exited successfully. The focused axiom audit for the nine new theorem
  declarations reports `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 focused §1.12.3 reverse first-suffix window shift:
  added `inverseSquareSingleReverseAfter4096CandidateWindowLower`,
  `inverseSquareSingleReverseAfter4096CandidateWindowUpper`,
  `inverseSquareSingleReverseAfter4096Candidate_mem_after4096Window`, and
  `inverseSquareSingleReverseCandidateWindow_add_4096_term_mem_after4096Window`.
  These definitions and theorems close the first whole-window transition for
  the candidate-window suffix map: exact addition of `4096^{-2}` sends every
  start in the 1024-ulp high-prefix candidate window into a 512-ulp
  post-`4096` window at the next binary32 exponent. Added
  `CHAPTER01_REVERSE_SUMMATION_BOTTLENECK.md` to keep the remaining red
  dependency explicit and to record the no-4096-case-enumeration policy. Reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`; it
  exited successfully. A focused axiom audit for the two new theorem
  declarations reports `[propext, Classical.choice, Quot.sound]`. Reran source
  placeholder scans for `sorry`/`admit`/`axiom`/`unsafe`/`opaque` on the
  touched Lean files and `git diff --check` for the touched Chapter 1
  files/docs; all exited successfully. At this validation point, the broad
  `lake env lean examples/LibraryLookup.lean` check was blocked before the
  Chapter 1 checks by an unrelated existing failure while building
  `LeanFpAnalysis.FP.Analysis.Problem2_24`: the open goal was
  `4 < 2 ^ 1022` at `Problem2_24.lean:2611`.
- 2026-06-13 focused §1.12.3 reverse rounded first-suffix window enclosure:
  added `FloatingPointFormat.nearestRoundingToFinite_mem_Icc_of_finite_endpoints`
  and
  `inverseSquareSingleReverseCandidateWindow_round_4096_step_mem_after4096Window`.
  The generic endpoint lemma proves that nearest finite rounding cannot leave
  an interval with finite representable endpoints when the exact input lies in
  that interval. The Chapter 1 specialization applies it to the exact-add
  post-`4096` window, proving that the rounded first suffix step from any start
  in the high-prefix candidate window remains in the 512-ulp post-`4096`
  window. This closes the local D2.2 rounding-enclosure dependency in
  `CHAPTER01_REVERSE_SUMMATION_BOTTLENECK.md`; the remaining suffix work is
  whole-window propagation after that first rounded transition, not a
  low-index case split. Reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`; it
  exited successfully. A focused axiom audit for the two new theorem
  declarations reports `[propext, Classical.choice, Quot.sound]`. Reran source
  placeholder scans for `sorry`/`admit`/`axiom`/`unsafe`/`opaque` on the
  touched Lean files and `git diff --check` for the touched Chapter 1
  files/docs; all exited successfully.
- 2026-06-13 focused §1.12.3 reverse post-`4096` suffix reduction:
  added `inverseSquareSingleReverseAfter4096WindowMapsToPrinted` and
  `inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_after4096Window`.
  The new predicate states the remaining whole-window suffix obligation after
  the first rounded `4096^{-2}` step. The reduction theorem unfolds exactly
  one reverse accumulator step, applies the rounded first-step window enclosure,
  and hands the remaining `4095` additions to the post-`4096` window predicate.
  This moves the open suffix target past the first rounded transition without
  enumerating suffix indices. Reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`; it
  exited successfully. A focused axiom audit for the new predicate/reduction
  declarations reports `[propext, Classical.choice, Quot.sound]`. Reran source
  placeholder scans for `sorry`/`admit`/`axiom`/`unsafe`/`opaque` on the
  touched Lean files and `git diff --check` for the touched Chapter 1
  files/docs; all exited successfully.
- 2026-06-13 focused §1.12.3 reverse post-`4095` suffix reduction:
  added `inverseSquareSingleReverseAfter4095CandidateWindowLower`,
  `inverseSquareSingleReverseAfter4095CandidateWindowUpper`,
  `inverseSquareSingleReverseAfter4095Candidate_mem_after4095Window`,
  `inverseSquareSingleReverseAfter4096Window_add_4095_term_mem_after4095Window`,
  `inverseSquareSingleReverseAfter4096Window_round_4095_step_mem_after4095Window`,
  `inverseSquareSingleReverseAfter4095WindowMapsToPrinted`, and
  `inverseSquareSingleReverseAfter4096WindowMapsToPrinted_of_after4095Window`.
  Since `4095^{-2}` is slightly larger than 2049 ulps in the exponent-`-11`
  band, the post-`4095` whole-window target is the asymmetric binary32 window
  `[candidate - 512 ulps, candidate + 513 ulps]`. The exact-add theorem maps
  the post-`4096` window into that interval, the nearest-finite endpoint
  enclosure keeps the rounded step inside it, and the suffix obligation is
  reduced to the post-`4095` predicate without enumerating suffix indices.
  Reran `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`;
  it exited successfully. A focused axiom audit for the rounded-step theorem
  and post-window reduction reports `[propext, Classical.choice, Quot.sound]`.
  Reran source placeholder scans for `sorry`/`admit`/`axiom`/`unsafe`/`opaque`
  on the touched Lean files and `git diff --check` for the touched Chapter 1
  files/docs; all exited successfully. Reran
  `lake env lean examples/LibraryLookup.lean`; it exited successfully with
  `51878` output lines.
- 2026-06-13 focused §1.12.3 reverse before-`2048` band handoff:
  added `inverseSquareSingleReverseBefore2048CandidateWindowLower`,
  `inverseSquareSingleReverseBefore2048CandidateWindowUpper`,
  `inverseSquareSingleReverseBefore2048Candidate_mem_before2048Window`,
  `inverseSquareSingleReverseAfter4095Band4094ToBefore2048Window`,
  `inverseSquareSingleReverseAfter4095Candidate_band4094_to_before2048_mem_before2048Window`,
  `inverseSquareSingleReverseBefore2048WindowMapsToPrinted`, and
  `inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_band4094_to_before2048Window`.
  The before-`2048` window is centered on the already-closed concrete
  `4094^{-2}, ..., 2049^{-2}` chunk target. The new reduction theorem splits
  the post-`4095` suffix at `4094 = 2046 + 2048`, isolating the whole-window
  band certificate from the remaining before-`2048` suffix certificate. This
  keeps the route chunk-based rather than index-by-index. Reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`; it
  exited successfully. A focused axiom audit for the new before-`2048` window
  membership theorem and band-handoff reduction reports
  `[propext, Classical.choice, Quot.sound]`. Reran source placeholder scans for
  `sorry`/`admit`/`axiom`/`unsafe`/`opaque` on the touched Lean/lookup files and
  `git diff --check` for the touched Chapter 1 files/docs; all exited
  successfully. Reran `lake env lean examples/LibraryLookup.lean`; it exited
  successfully with `51894` output lines.
- 2026-06-13 focused §1.12.3 reverse `4094..2049` window-band endpoints:
  added
  `inverseSquareSingleReverseAfter4095Band4094To2049WindowEndpointCertificateBool`,
  `inverseSquareSingleReverseAfter4095Band4094To2049WindowEndpointCertificateBool_eq_true`,
  `inverseSquareSingleReverseAfter4095Band4094To2049WindowEndpointCertificate`,
  `inverseSquareSingleReverseAfter4095WindowLower_band4094_to_before2048_eq`,
  and
  `inverseSquareSingleReverseAfter4095WindowUpper_band4094_to_before2048_eq`.
  The checked endpoint certificate reuses the same 2046-term same-exponent
  chunk and verifies that both post-`4095` window endpoints stay in the normal
  mantissa range throughout. The lower and upper endpoint theorems then prove
  exact propagation to the two before-`2048` window endpoints. This closes the
  endpoint landing part of D2a; the remaining D2a work is the monotonicity or
  interior-window lift from endpoints to arbitrary starts in the post-`4095`
  window. Reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`; it
  exited successfully. A focused axiom audit for the endpoint certificate and
  both endpoint propagation theorems reports
  `[propext, Classical.choice, Quot.sound]`. Reran source placeholder scans for
  `sorry`/`admit`/`axiom`/`unsafe`/`opaque` on the touched Lean/lookup files and
  `git diff --check` for the touched Chapter 1 files/docs; all exited
  successfully. Reran `lake env lean examples/LibraryLookup.lean`; it exited
  successfully with `51942` output lines.
- 2026-06-13 focused §1.12.3 reverse window-band midpoint infrastructure:
  added `FloatingPointFormat.finiteSystem_lt_right_adjacent_le_left`,
  `FloatingPointFormat.right_adjacent_le_finiteSystem_of_left_lt`,
  `FloatingPointFormat.nearestRoundingToFinite_ge_of_adjacent_midpoint`, and
  `FloatingPointFormat.nearestRoundingToFinite_le_of_adjacent_midpoint`.
  These generic lemmas convert positive adjacent-normalized no-between facts
  into finite-system exclusions, including zero and subnormal cases, and prove
  that nearest finite rounding cannot cross a lower or upper adjacent target
  once the exact input is on the target side of the midpoint. This closes the
  generic midpoint-exclusion tool needed for the D2a interior lift; what
  remains is threading it through the `4094^{-2}, ..., 2049^{-2}` prefix
  induction. Reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`; it
  exited successfully. A focused axiom audit for the four new rounding lemmas
  reports `[propext, Classical.choice, Quot.sound]`. Reran
  `lake env lean examples/LibraryLookup.lean`; it exited successfully with
  `51963` output lines.
- 2026-06-13 focused §1.12.3 reverse `4094..2049` window-band induction
  closure: added the prefix-window endpoints
  `inverseSquareSingleReverseAfter4095BandWindowLower` and
  `inverseSquareSingleReverseAfter4095BandWindowUpper`, endpoint identities at
  zero and at `2046`, the real distance helpers
  `abs_sub_right_lt_abs_sub_left_of_le_of_right_closer` and
  `abs_sub_left_lt_abs_sub_right_of_le_of_left_closer`, the arbitrary-start
  one-step theorem
  `inverseSquareSingleReverseAfter4095BandWindow_round_step_mem`, the prefix
  induction theorem `inverseSquareSingleReverseAfter4095BandWindow_prefix_mem`,
  the closed band certificate
  `inverseSquareSingleReverseAfter4095Band4094ToBefore2048Window_closed`, and
  the direct reduction
  `inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before2048Window`.
  This closes D2a without proving 2046 separate suffix cases: the one-step
  theorem uses the endpoint certificate and adjacent-midpoint rounding
  exclusions, and induction carries every start in the post-`4095` window to
  the before-`2048` window. Reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`; it
  exited successfully. A focused axiom audit for the two real helpers, the
  one-step theorem, prefix induction, closed band certificate, and direct
  reduction reports `[propext, Classical.choice, Quot.sound]`. Reran
  `lake env lean examples/LibraryLookup.lean` with output redirected to
  `/private/tmp/chapter01_librarylookup.out`; it exited successfully with
  `52050` output lines. Reran the touched-file placeholder scan for
  `sorry`/`admit`/`axiom`/`unsafe`/`opaque`; it returned no matches. Reran
  `git diff --check` for the touched Lean, lookup, and Chapter 1 docs; it
  exited successfully.
- 2026-06-13 focused §1.12.3 reverse before-`2048` to before-`1024`
  whole-window suffix reduction: added the post-`2048` window
  `inverseSquareSingleReverseAfter2048CandidateWindowLower`/`Upper`, the
  rounded boundary theorem
  `inverseSquareSingleReverseBefore2048Window_round_2048_step_mem_after2048Window`,
  the post-`2048` suffix predicate
  `inverseSquareSingleReverseAfter2048WindowMapsToPrinted`, the before-`1024`
  window endpoints, the `2047^{-2}, ..., 1025^{-2}` endpoint certificate
  `inverseSquareSingleReverseAfter2048Band2047To1025WindowEndpointCertificate`,
  the arbitrary-start one-step theorem
  `inverseSquareSingleReverseAfter2048BandWindow_round_step_mem`, the prefix
  induction theorem `inverseSquareSingleReverseAfter2048BandWindow_prefix_mem`,
  the closed band certificate
  `inverseSquareSingleReverseAfter2048Band2047ToBefore1024Window_closed`, and
  the direct reductions
  `inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before1024Window`
  and `inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before1024Window`.
  This moves D2 from a before-`2048` whole-window suffix obligation to the
  smaller `inverseSquareSingleReverseBefore1024WindowMapsToPrinted` obligation,
  again without enumerating suffix steps one by one. Reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`; it
  exited successfully. A focused axiom audit for the rounded boundary theorem,
  endpoint certificate, one-step theorem, prefix induction, closed band
  certificate, and direct reductions reports only baseline axioms
  `[propext, Classical.choice, Quot.sound]` for theorem wrappers; the checked
  certificate equality itself reports `[propext]`. Reran
  `lake env lean examples/LibraryLookup.lean` with output redirected to
  `/private/tmp/chapter01_librarylookup_after2048.out`; it exited successfully
  with `52181` output lines. Reran the touched-file placeholder scan for
  `sorry`/`admit`/`axiom`/`unsafe`/`opaque`; it returned no matches. Reran
  `git diff --check` for the touched Lean, lookup, and Chapter 1 docs; it
  exited successfully.
- 2026-06-13 focused §1.12.3 reverse before-`1024` to before-`512`
  whole-window suffix reduction: added the post-`1024` window
  `inverseSquareSingleReverseAfter1024CandidateWindowLower`/`Upper`, the
  rounded boundary theorem
  `inverseSquareSingleReverseBefore1024Window_round_1024_step_mem_after1024Window`,
  the post-`1024` suffix predicate
  `inverseSquareSingleReverseAfter1024WindowMapsToPrinted`, the before-`512`
  window endpoints, the `1023^{-2}, ..., 513^{-2}` endpoint certificate
  `inverseSquareSingleReverseAfter1024Band1023To513WindowEndpointCertificate`,
  the arbitrary-start one-step theorem
  `inverseSquareSingleReverseAfter1024BandWindow_round_step_mem`, the prefix
  induction theorem `inverseSquareSingleReverseAfter1024BandWindow_prefix_mem`,
  the closed band certificate
  `inverseSquareSingleReverseAfter1024Band1023ToBefore512Window_closed`, and
  the direct reductions
  `inverseSquareSingleReverseBefore1024WindowMapsToPrinted_of_before512Window`,
  `inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before512Window`,
  and `inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before512Window`.
  This moves D2 from a before-`1024` whole-window suffix obligation to the
  smaller `inverseSquareSingleReverseBefore512WindowMapsToPrinted` obligation,
  again by endpoint windows plus prefix induction rather than suffix
  enumeration. Reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`; it
  exited successfully. A focused axiom audit for the rounded boundary theorem,
  endpoint certificate, one-step theorem, prefix induction, closed band
  certificate, and direct reductions reports only baseline axioms
  `[propext, Classical.choice, Quot.sound]` for theorem wrappers; the checked
  certificate equality itself reports `[propext]`. While rerunning
  `examples/LibraryLookup.lean`, the existing import graph exposed an unrelated
  stale proof in `LeanFpAnalysis/FP/Algorithms/OrderingExamples.lean`; replaced
  its fragile exact-model induction tail with an explicit `calc`, after which
  `lake build LeanFpAnalysis.FP.Algorithms.OrderingExamples` passed. Reran
  `lake env lean examples/LibraryLookup.lean` with output redirected to
  `/private/tmp/chapter01_librarylookup_after1024.out`; it exited successfully
  with `52366` output lines. Reran the touched-file placeholder scan for
  `sorry`/`admit`/`axiom`/`unsafe`/`opaque`; it returned no matches. Reran
  `git diff --check` for the touched Lean, lookup, and Chapter 1 docs; it
  exited successfully.
- 2026-06-13 focused §1.12.3 reverse before-`512` to before-`256`
  whole-window suffix reduction: added the post-`512` window
  `inverseSquareSingleReverseAfter512CandidateWindowLower`/`Upper`, the
  rounded boundary theorem
  `inverseSquareSingleReverseBefore512Window_round_512_step_mem_after512Window`,
  the post-`512` suffix predicate
  `inverseSquareSingleReverseAfter512WindowMapsToPrinted`, the before-`256`
  window endpoints, the `511^{-2}, ..., 257^{-2}` endpoint certificate
  `inverseSquareSingleReverseAfter512Band511To257WindowEndpointCertificate`,
  the arbitrary-start one-step theorem
  `inverseSquareSingleReverseAfter512BandWindow_round_step_mem`, the prefix
  induction theorem `inverseSquareSingleReverseAfter512BandWindow_prefix_mem`,
  the closed band certificate
  `inverseSquareSingleReverseAfter512Band511ToBefore256Window_closed`, and the
  direct reductions
  `inverseSquareSingleReverseBefore512WindowMapsToPrinted_of_before256Window`,
  `inverseSquareSingleReverseBefore1024WindowMapsToPrinted_of_before256Window`,
  `inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before256Window`,
  and `inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before256Window`.
  This moves D2 from a before-`512` whole-window suffix obligation to the
  smaller `inverseSquareSingleReverseBefore256WindowMapsToPrinted` obligation,
  still by endpoint windows plus prefix induction rather than suffix
  enumeration. Reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`; it
  exited successfully. A focused axiom audit for the rounded boundary theorem,
  endpoint certificate, one-step theorem, prefix induction, closed band
  certificate, and direct reductions reports only baseline axioms
  `[propext, Classical.choice, Quot.sound]` for theorem wrappers; the checked
  certificate equality itself reports `[propext]`. Rebuilt the lookup import
  dependency `LeanFpAnalysis.FP.Algorithms.RandNLA.UniformRowSamplingFP`, then
  reran `lake env lean examples/LibraryLookup.lean` with output redirected to
  `/private/tmp/chapter01_librarylookup_after512.out`; it exited successfully
  with `52452` output lines. Reran the touched-file placeholder scan for
  `sorry`/`admit`/`axiom`/`unsafe`/`opaque`; it returned no matches. Reran
  `git diff --check` for the touched Lean, lookup, and Chapter 1 docs; it
  exited successfully.
- 2026-06-13 focused §1.12.3 reverse before-`256` to before-`128`
  whole-window suffix reduction: added the post-`256` window
  `inverseSquareSingleReverseAfter256CandidateWindowLower`/`Upper`, the
  rounded boundary theorem
  `inverseSquareSingleReverseBefore256Window_round_256_step_mem_after256Window`,
  the post-`256` suffix predicate
  `inverseSquareSingleReverseAfter256WindowMapsToPrinted`, the before-`128`
  window endpoints, the `255^{-2}, ..., 129^{-2}` endpoint certificate
  `inverseSquareSingleReverseAfter256Band255To129WindowEndpointCertificate`,
  the arbitrary-start one-step theorem
  `inverseSquareSingleReverseAfter256BandWindow_round_step_mem`, the prefix
  induction theorem `inverseSquareSingleReverseAfter256BandWindow_prefix_mem`,
  the closed band certificate
  `inverseSquareSingleReverseAfter256Band255ToBefore128Window_closed`, and the
  direct reductions
  `inverseSquareSingleReverseBefore256WindowMapsToPrinted_of_before128Window`,
  `inverseSquareSingleReverseBefore512WindowMapsToPrinted_of_before128Window`,
  `inverseSquareSingleReverseBefore1024WindowMapsToPrinted_of_before128Window`,
  `inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before128Window`,
  `inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before128Window`,
  and `inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before128Window`.
  This moves D2 from a before-`256` whole-window suffix obligation to the
  smaller `inverseSquareSingleReverseBefore128WindowMapsToPrinted` obligation,
  again by endpoint windows plus prefix induction rather than suffix
  enumeration. Reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`; it
  exited successfully. A focused axiom audit for the rounded boundary theorem,
  endpoint certificate, one-step theorem, prefix induction, closed band
  certificate, and direct reductions reports only baseline axioms
  `[propext, Classical.choice, Quot.sound]` for theorem wrappers; the checked
  certificate equality itself reports `[propext]`. Reran
  `lake env lean examples/LibraryLookup.lean` with output redirected to
  `/private/tmp/chapter01_librarylookup_after256.out`; it exited successfully
  with `52592` output lines. Reran the touched-file placeholder scan for
  `sorry`/`admit`/`axiom`/`unsafe`/`opaque`; it returned no matches. Reran the
  tracked-file `git diff --check` for the tracked lookup surface; it returned
  no whitespace diagnostics, and separate no-index whitespace checks for the
  untracked Chapter 1 Lean/docs returned no diagnostics.
- 2026-06-13 focused §1.12.3 reverse before-`128` to before-`64`
  whole-window suffix reduction: added the post-`128` window
  `inverseSquareSingleReverseAfter128CandidateWindowLower`/`Upper`, the
  rounded boundary theorem
  `inverseSquareSingleReverseBefore128Window_round_128_step_mem_after128Window`,
  the post-`128` suffix predicate
  `inverseSquareSingleReverseAfter128WindowMapsToPrinted`, the before-`64`
  window endpoints, the `127^{-2}, ..., 65^{-2}` endpoint certificate
  `inverseSquareSingleReverseAfter128Band127To65WindowEndpointCertificate`,
  the arbitrary-start one-step theorem
  `inverseSquareSingleReverseAfter128BandWindow_round_step_mem`, the prefix
  induction theorem `inverseSquareSingleReverseAfter128BandWindow_prefix_mem`,
  the closed band certificate
  `inverseSquareSingleReverseAfter128Band127ToBefore64Window_closed`, and the
  direct reductions
  `inverseSquareSingleReverseBefore128WindowMapsToPrinted_of_before64Window`,
  `inverseSquareSingleReverseBefore256WindowMapsToPrinted_of_before64Window`,
  `inverseSquareSingleReverseBefore512WindowMapsToPrinted_of_before64Window`,
  `inverseSquareSingleReverseBefore1024WindowMapsToPrinted_of_before64Window`,
  `inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before64Window`,
  `inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before64Window`,
  and `inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before64Window`.
  This moves D2 from a before-`128` whole-window suffix obligation to the
  smaller `inverseSquareSingleReverseBefore64WindowMapsToPrinted` obligation,
  still by endpoint windows plus prefix induction rather than suffix
  enumeration. Reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`; it
  exited successfully. A focused axiom audit for the rounded boundary theorem,
  endpoint certificate, one-step theorem, prefix induction, closed band
  certificate, and direct reductions reports only baseline axioms
  `[propext, Classical.choice, Quot.sound]` for theorem wrappers; the checked
  certificate equality itself reports `[propext]`. Reran
  `lake env lean examples/LibraryLookup.lean` with output redirected to
  `/private/tmp/chapter01_librarylookup_after128.out`; it exited successfully
  with `52696` output lines.
- 2026-06-13 focused §1.12.3 reverse before-`64` to before-`32`
  whole-window suffix reduction: added the post-`64` window
  `inverseSquareSingleReverseAfter64CandidateWindowLower`/`Upper`, the rounded
  boundary theorem
  `inverseSquareSingleReverseBefore64Window_round_64_step_mem_after64Window`,
  the post-`64` suffix predicate
  `inverseSquareSingleReverseAfter64WindowMapsToPrinted`, the before-`32`
  window endpoints, the `63^{-2}, ..., 33^{-2}` endpoint certificate
  `inverseSquareSingleReverseAfter64Band63To33WindowEndpointCertificate`, the
  arbitrary-start one-step theorem
  `inverseSquareSingleReverseAfter64BandWindow_round_step_mem`, the prefix
  induction theorem `inverseSquareSingleReverseAfter64BandWindow_prefix_mem`,
  the closed band certificate
  `inverseSquareSingleReverseAfter64Band63ToBefore32Window_closed`, and the
  direct reductions
  `inverseSquareSingleReverseBefore64WindowMapsToPrinted_of_before32Window`,
  `inverseSquareSingleReverseBefore128WindowMapsToPrinted_of_before32Window`,
  `inverseSquareSingleReverseBefore256WindowMapsToPrinted_of_before32Window`,
  `inverseSquareSingleReverseBefore512WindowMapsToPrinted_of_before32Window`,
  `inverseSquareSingleReverseBefore1024WindowMapsToPrinted_of_before32Window`,
  `inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before32Window`,
  `inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before32Window`,
  and `inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before32Window`.
  This moves D2 from a before-`64` whole-window suffix obligation to the
  smaller `inverseSquareSingleReverseBefore32WindowMapsToPrinted` obligation,
  still by endpoint windows plus prefix induction rather than suffix
  enumeration. Reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`; it
  exited successfully. A focused axiom audit for the rounded boundary theorem,
  endpoint certificate, one-step theorem, prefix induction, closed band
  certificate, and direct reductions reports only baseline axioms
  `[propext, Classical.choice, Quot.sound]` for theorem wrappers; the checked
  certificate equality itself reports `[propext]`. Reran
  `lake env lean examples/LibraryLookup.lean` with output redirected to
  `/private/tmp/chapter01_librarylookup_after64.out`; it exited successfully
  with `52804` output lines. Reran the touched-file placeholder scan for
  `sorry`/`admit`/`axiom`/`unsafe`/`opaque`; it returned no matches.
- 2026-06-13 focused §1.12.3 reverse before-`32` to before-`16`
  whole-window suffix reduction: added the post-`32` window
  `inverseSquareSingleReverseAfter32CandidateWindowLower`/`Upper`, the rounded
  boundary theorem
  `inverseSquareSingleReverseBefore32Window_round_32_step_mem_after32Window`,
  the post-`32` suffix predicate
  `inverseSquareSingleReverseAfter32WindowMapsToPrinted`, the before-`16`
  window endpoints, the `31^{-2}, ..., 17^{-2}` endpoint certificate
  `inverseSquareSingleReverseAfter32Band31To17WindowEndpointCertificate`, the
  arbitrary-start one-step theorem
  `inverseSquareSingleReverseAfter32BandWindow_round_step_mem`, the prefix
  induction theorem `inverseSquareSingleReverseAfter32BandWindow_prefix_mem`,
  the closed band certificate
  `inverseSquareSingleReverseAfter32Band31ToBefore16Window_closed`, and the
  direct reductions
  `inverseSquareSingleReverseBefore32WindowMapsToPrinted_of_before16Window`,
  `inverseSquareSingleReverseBefore64WindowMapsToPrinted_of_before16Window`,
  `inverseSquareSingleReverseBefore128WindowMapsToPrinted_of_before16Window`,
  `inverseSquareSingleReverseBefore256WindowMapsToPrinted_of_before16Window`,
  `inverseSquareSingleReverseBefore512WindowMapsToPrinted_of_before16Window`,
  `inverseSquareSingleReverseBefore1024WindowMapsToPrinted_of_before16Window`,
  `inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before16Window`,
  `inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before16Window`,
  and `inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before16Window`.
  This moves D2 from a before-`32` whole-window suffix obligation to the
  smaller `inverseSquareSingleReverseBefore16WindowMapsToPrinted` obligation,
  still by endpoint windows plus prefix induction rather than suffix
  enumeration. Reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`; it
  exited successfully. A focused axiom audit for the rounded boundary theorem,
  endpoint certificate, one-step theorem, prefix induction, closed band
  certificate, and direct reductions reports only baseline axioms
  `[propext, Classical.choice, Quot.sound]` for theorem wrappers; the checked
  certificate equality itself reports `[propext]`. Reran
  `lake env lean examples/LibraryLookup.lean` with output redirected to
  `/private/tmp/chapter01_librarylookup_after32.out`; it exited successfully
  with `52922` output lines. Reran the touched-file placeholder scan for
  `sorry`/`admit`/`axiom`/`unsafe`/`opaque`; it returned no matches.
- 2026-06-13 focused §1.12.3 reverse before-`16` to before-`8`
  whole-window suffix reduction: added the post-`16` window
  `inverseSquareSingleReverseAfter16CandidateWindowLower`/`Upper`, the rounded
  boundary theorem
  `inverseSquareSingleReverseBefore16Window_round_16_step_mem_after16Window`,
  the post-`16` suffix predicate
  `inverseSquareSingleReverseAfter16WindowMapsToPrinted`, the before-`8`
  window endpoints, the `15^{-2}, ..., 9^{-2}` endpoint certificate
  `inverseSquareSingleReverseAfter16Band15To9WindowEndpointCertificate`, the
  arbitrary-start one-step theorem
  `inverseSquareSingleReverseAfter16BandWindow_round_step_mem`, the prefix
  induction theorem `inverseSquareSingleReverseAfter16BandWindow_prefix_mem`,
  the closed band certificate
  `inverseSquareSingleReverseAfter16Band15ToBefore8Window_closed`, and the
  direct reductions
  `inverseSquareSingleReverseBefore16WindowMapsToPrinted_of_before8Window`,
  `inverseSquareSingleReverseBefore32WindowMapsToPrinted_of_before8Window`,
  `inverseSquareSingleReverseBefore64WindowMapsToPrinted_of_before8Window`,
  `inverseSquareSingleReverseBefore128WindowMapsToPrinted_of_before8Window`,
  `inverseSquareSingleReverseBefore256WindowMapsToPrinted_of_before8Window`,
  `inverseSquareSingleReverseBefore512WindowMapsToPrinted_of_before8Window`,
  `inverseSquareSingleReverseBefore1024WindowMapsToPrinted_of_before8Window`,
  `inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before8Window`,
  `inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before8Window`,
  and `inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before8Window`.
  This moves D2 from a before-`16` whole-window suffix obligation to the
  smaller `inverseSquareSingleReverseBefore8WindowMapsToPrinted` obligation,
  again by endpoint windows plus prefix induction rather than suffix
  enumeration. Reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`; it
  exited successfully. A focused axiom audit for the rounded boundary theorem,
  endpoint certificate, one-step theorem, prefix induction, closed band
  certificate, and direct reductions reports only baseline axioms
  `[propext, Classical.choice, Quot.sound]` for theorem wrappers; the checked
  certificate equality itself reports `[propext]`. Reran
  `lake env lean examples/LibraryLookup.lean` with output redirected to
  `/private/tmp/chapter01_librarylookup_after16.out`; it exited successfully
  with `53054` output lines. Reran the touched-file placeholder scan for
  `sorry`/`admit`/`axiom`/`unsafe`/`opaque`; it returned no matches.
- 2026-06-13 focused §1.12.3 reverse before-`8` to before-`4`
  whole-window suffix reduction: added the post-`8` window
  `inverseSquareSingleReverseAfter8CandidateWindowLower`/`Upper`, the rounded
  boundary theorem
  `inverseSquareSingleReverseBefore8Window_round_8_step_mem_after8Window`,
  the post-`8` suffix predicate
  `inverseSquareSingleReverseAfter8WindowMapsToPrinted`, the before-`4`
  window endpoints, the `7^{-2}, 6^{-2}, 5^{-2}` endpoint certificate
  `inverseSquareSingleReverseAfter8Band7To5WindowEndpointCertificate`, the
  arbitrary-start one-step theorem
  `inverseSquareSingleReverseAfter8BandWindow_round_step_mem`, the prefix
  induction theorem `inverseSquareSingleReverseAfter8BandWindow_prefix_mem`,
  the closed band certificate
  `inverseSquareSingleReverseAfter8Band7ToBefore4Window_closed`, and the
  direct reductions
  `inverseSquareSingleReverseBefore8WindowMapsToPrinted_of_before4Window`,
  `inverseSquareSingleReverseBefore16WindowMapsToPrinted_of_before4Window`,
  `inverseSquareSingleReverseBefore32WindowMapsToPrinted_of_before4Window`,
  `inverseSquareSingleReverseBefore64WindowMapsToPrinted_of_before4Window`,
  `inverseSquareSingleReverseBefore128WindowMapsToPrinted_of_before4Window`,
  `inverseSquareSingleReverseBefore256WindowMapsToPrinted_of_before4Window`,
  `inverseSquareSingleReverseBefore512WindowMapsToPrinted_of_before4Window`,
  `inverseSquareSingleReverseBefore1024WindowMapsToPrinted_of_before4Window`,
  `inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before4Window`,
  `inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before4Window`,
  and `inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before4Window`.
  This moves D2 from a before-`8` whole-window suffix obligation to the final
  `inverseSquareSingleReverseBefore4WindowMapsToPrinted` obligation, again by
  endpoint windows plus prefix induction rather than suffix enumeration. Reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`; it
  exited successfully. A focused axiom audit for the rounded boundary theorem,
  endpoint certificate, one-step theorem, prefix induction, closed band
  certificate, and direct reductions reports only baseline axioms
  `[propext, Classical.choice, Quot.sound]` for theorem wrappers; the checked
  certificate equality itself reports `[propext]`. Reran
  `lake env lean examples/LibraryLookup.lean` with output redirected to
  `/private/tmp/chapter01_librarylookup_after8.out`; it exited successfully
  with `53254` output lines. Reran the touched-file placeholder scan for
  `sorry`/`admit`/`axiom`/`unsafe`/`opaque`; it returned no matches.
- 2026-06-13 focused §1.12.3 reverse final before-`4` whole-window suffix
  closure: added post-`4` and post-`3` endpoint windows
  `inverseSquareSingleReverseAfter4WindowLower`/`Upper` and
  `inverseSquareSingleReverseAfter3WindowLower`/`Upper`, the exact and rounded
  `4^{-2}` interval step
  `inverseSquareSingleReverseBefore4Window_add_4_term_mem_after4Window` and
  `inverseSquareSingleReverseBefore4Window_round_4_step_mem_after4Window`, the
  arbitrary-start rounded `3^{-2}` window step
  `inverseSquareSingleReverseAfter4Window_round_3_step_mem_after3Window`, and
  the tie-to-even `2^{-2}` collapse
  `inverseSquareSingleReverseAfter3Window_round_2_step_eq_after2`.  These
  compose with the existing exact `1^{-2}` final step to prove
  `inverseSquareSingleReverseBefore4WindowMapsToPrinted_closed`, then close
  `inverseSquareSingleReverseAfter8WindowMapsToPrinted_closed`,
  `inverseSquareSingleReverseBefore8WindowMapsToPrinted_closed`,
  `inverseSquareSingleReverseCandidateWindowMapsToPrinted_closed`, and
  `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_mem_candidateWindow_closed`.
  This closes D2 by endpoint windows and adjacent-bracket round-to-even
  reasoning, not by enumerating suffix cases. Reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`; it
  exited successfully. A focused axiom audit for the five new closed wrappers
  reported only `[propext, Classical.choice, Quot.sound]`. Reran
  `lake env lean examples/LibraryLookup.lean` with output redirected to
  `/private/tmp/chapter01_librarylookup_before4.out`; it exited successfully
  with `53360` output lines. Reran the touched-file placeholder scan for
  `sorry`/`admit`/`axiom`/`unsafe`/`opaque`; it returned no matches, and
  `git diff --check` reported no whitespace errors on the touched Lean,
  lookup, and documentation files.
- 2026-06-13 focused §1.12.3 reverse high-prefix candidate-window margin
  transfer: added the exact candidate-window margin
  `inverseSquareSingleReverseHighPrefixCandidateWindowMargin`, the explicit
  shifted lower-bound margin
  `inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound`,
  and the bridges
  `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_abs_error_le_candidateWindowMargin`,
  `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_abs_error_le_candidateWindowMarginShiftedLowerBound`,
  and
  `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_abs_error_le_candidateWindowMarginShiftedLowerBound_closed`.
  This reduces D1 to a single absolute-error certificate for the rounded
  high-prefix state against the exact high-prefix mass; the `4096` low-index
  suffix route remains closed by the candidate-window suffix theorem, so no
  suffix-case enumeration is being introduced. Reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`; it
  exited successfully. Reran `lake env lean examples/LibraryLookup.lean` with
  output redirected to
  `/private/tmp/chapter01_librarylookup_highprefix_margin.out`; it exited
  successfully with `53436` output lines. A focused axiom audit for the new
  candidate-window margin declarations and closed wrapper reported only
  `[propext, Classical.choice, Quot.sound]`. Reran the touched-file placeholder
  scan for `sorry`/`admit`/`axiom`/`unsafe`/`opaque`; it returned no matches,
  and `git diff --check` reported no whitespace errors on the touched Lean,
  lookup, and documentation files.
- 2026-06-13 focused §1.12.3 reverse D1 named-target and candidate consistency
  check: added the named high-prefix target
  `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowMarginTarget`,
  proved the observed candidate satisfies that target's explicit margin by
  `inverseSquareSingleReverseTenPowNineHighPrefixCandidate_abs_error_le_candidateWindowMarginShiftedLowerBound`,
  proved the old equality-to-candidate route implies the named target by
  `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowMarginTarget_of_eq_candidate`,
  added the route guard
  `inverseSquareSingleReverseTenPowNineHighPrefix_singleGammaGuard_not_valid`
  proving the single-precision `gamma (n-1)` recursive-sum guard is false for
  the `10^9 - 4096` high-prefix length,
  and added the named candidate-window/printed-value bridges
  `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_candidateWindowMarginTarget`
  and
  `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_candidateWindowMarginTarget_closed`.
  D1 is still open for the actual rounded high-prefix state, but the target is
  now a single checkable proposition with a proved consistency check against the
  observed binary32 candidate. Validation: `lake build
  LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation` passed; `lake env
  lean examples/LibraryLookup.lean` passed with output redirected to
  `/private/tmp/chapter01_librarylookup_d1_target.out`, producing `53499`
  output lines; a focused axiom audit for the new D1 target declarations and
  bridges reported only `[propext, Classical.choice, Quot.sound]`; the
  touched-file placeholder scan for `sorry`/`admit`/`axiom`/`unsafe`/`opaque`
  returned no matches; and `git diff --check` reported no whitespace errors on
  the touched Lean, lookup, and documentation files. Follow-up route-guard
  validation: reran `lake build
  LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`; it passed.
  Rebuilt `LeanFpAnalysis.FP.Analysis` to refresh the aggregate lookup import,
  then reran `lake env lean examples/LibraryLookup.lean` with output redirected
  to `/private/tmp/chapter01_librarylookup_d1_route_guard.out`; it passed with
  `53536` output lines and lists
  `inverseSquareSingleReverseTenPowNineHighPrefix_singleGammaGuard_not_valid`.
  A focused axiom audit for the route guard reported only `[propext,
  Classical.choice, Quot.sound]`. Gamma-valid guard follow-up: added
  `inverseSquareSingleReverseTenPowNineHighPrefix_singleGammaValid_not_valid`,
  the direct `gammaValid fp` obstruction under `fp.u = 2^-24`; reran `lake
  build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`, which
  passed; reran `lake env lean examples/LibraryLookup.lean` with output
  redirected to `/private/tmp/chapter01_librarylookup_d1_gamma_valid_guard.out`,
  producing `53574` output lines and listing both guard theorems; and a focused
  axiom audit for both guards reported only `[propext, Classical.choice,
  Quot.sound]`. Finite-format foothold follow-up: added
  `inverseSquareSingleReverseAccumulatorFrom_finiteSystem_of_start` and
  `inverseSquareSingleReverseTenPowNineHighPrefixState_finiteSystem`, proving
	  the actual rounded high-prefix state is an IEEE-single finite-system value;
	  reran `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`,
	  which passed; reran `lake env lean examples/LibraryLookup.lean` with output
	  redirected to `/private/tmp/chapter01_librarylookup_d1_finite_system.out`,
	  producing `53619` output lines and listing both finite-system theorems; and a
	  focused axiom audit for both finite-system theorems reported only `[propext,
	  Classical.choice, Quot.sound]`. Finite-cell guard follow-up: added
	  `inverseSquareSingleReverseHighPrefixCandidateWindowLowerPred`,
	  `inverseSquareSingleReverseHighPrefixCandidateWindowUpperSucc`,
	  `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuard`,
	  `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuard_of_eq_candidate`,
	  `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_cellGuard`,
	  and
	  `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_candidateWindowCellGuard_closed`,
	  proving that the actual finite-system high-prefix state only needs to satisfy
	  two strict predecessor/successor endpoint inequalities to force candidate
	  window membership and hence Higham's printed reverse accumulator. Reran
	  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`; it
	  passed. Reran `lake env lean examples/LibraryLookup.lean` with output
	  redirected to `/private/tmp/chapter01_librarylookup_d1_cell_guard.out`,
	  producing `53676` output lines and listing the new cell-guard names. A
	  focused axiom audit for the new guard route reported only `[propext,
	  Classical.choice, Quot.sound]`. Monotonicity follow-up: added
	  `FloatingPointFormat.finiteRoundToEvenOp_add_ge_left_of_finiteSystem_of_nonneg`,
	  `inverseSquareSingleForwardStep_ge_self_of_finiteSystem`,
	  `inverseSquareSingleReverseAccumulatorFrom_start_le_of_finiteSystem`,
	  `inverseSquareSingleReverseAccumulatorFrom_nonneg_of_start_nonneg`, and
	  `inverseSquareSingleReverseTenPowNineHighPrefixState_nonneg`, proving that a
	  rounded positive reverse-prefix step cannot decrease a finite accumulator and
	  that the actual high-prefix state is nonnegative. Reran `lake build
	  LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`; it passed. Reran
	  `lake build LeanFpAnalysis.FP` to refresh the aggregate lookup import; it
	  passed with unrelated pre-existing linter warnings. Reran `lake env lean
	  examples/LibraryLookup.lean` with output redirected to
	  `/private/tmp/chapter01_librarylookup_d1_monotone.out`, producing `53961`
	  output lines and listing the new monotonicity names. A focused axiom audit
	  for the new monotonicity layer reported only `[propext, Classical.choice,
	  Quot.sound]`. Error-envelope follow-up: added
	  `FloatingPointFormat.finiteRoundToEvenOp_add_abs_error_le_right_of_finiteSystem_of_nonneg`,
	  `FloatingPointFormat.finiteRoundToEvenOp_add_le_left_add_two_mul_right_of_finiteSystem_of_nonneg`,
	  `inverseSquareSingleForwardStep_abs_error_le_term_of_finiteSystem`,
	  `inverseSquareSingleForwardStep_le_self_add_two_mul_term_of_finiteSystem`,
	  `inverseSquareSingleReverseAccumulatorFrom_le_start_add_two_mul_exact_zero_start`,
	  `inverseSquareSingleReverseTenPowNineHighPrefixState_le_two_mul_exact`, and
	  `inverseSquareSingleReverseTenPowNineHighPrefixState_le_inv_2048`. These prove
	  a one-step nearestness error bound, a one-step upper increment bound, and a
	  coarse block upper envelope for the actual high-prefix trace without
	  expanding the `10^9 - 4096` operations. Reran `lake build
	  LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`; it passed. Reran
	  `lake env lean examples/LibraryLookup.lean` with output redirected to
	  `/private/tmp/chapter01_librarylookup_d1_error_envelope.out`, producing
	  `54073` output lines and listing the new error-envelope names. A focused
	  axiom audit for the new envelope layer reported only `[propext,
	  Classical.choice, Quot.sound]`. High-prefix standard-model foothold:
	  added `inverseSquareTerm_ten_pow_nine_le_of_pos_le`,
	  `inverseSquareTerm_ten_pow_nine_ge_ieeeSingle_minNormal`,
	  `inverseSquareTerm_ge_ieeeSingle_minNormal_of_pos_le_ten_pow_nine`,
	  `inverseSquareSingleReverseAccumulatorFrom_le_of_le_steps`,
	  `inverseSquareSingleReverseTenPowNineHighPrefixState_prefix_le_highPrefix`,
	  `inverseSquareSingleReverseTenPowNineHighPrefixStep_exactInput_finiteNormalRange`,
	  and `inverseSquareSingleReverseTenPowNineHighPrefixStep_standardModel_lt`.
	  These prove, uniformly for every high-index prefix step, that the exact
	  addition input is binary32 finite-normal and therefore satisfies the
	  standard relative-error model with `|delta| < unitRoundoff`; this is a
	  quantified range theorem, not a per-index proof expansion. Local
	  absolute-error follow-up: added
	  `inverseSquareSingleReverseTenPowNineHighPrefixStep_abs_error_lt_unitRoundoff_mul_exactInput`
	  and
	  `inverseSquareSingleReverseTenPowNineHighPrefixStep_abs_error_lt_unitRoundoff_mul_coarse`.
	  The first rewrites the standard-model factor into a strict absolute-error
	  recurrence bound `|fl(s+t)-(s+t)| < u*(s+t)` for every high-prefix step;
	  the second applies the already proved high-prefix state envelope and
	  `2^-24` term bound to obtain the uniform coarse bound
	  `u*(1/2048 + 2^-24)` over the entire high-index prefix. Accumulated-envelope
	  follow-up: added `inverseSquareSingleReverseTenPowNineHighPrefixStepStdError`,
	  `inverseSquareSingleReverseTenPowNineHighPrefixStdErrorEnvelope`,
	  `inverseSquareSingleReverseTenPowNineHighPrefixStepStdError_nonneg`,
	  `inverseSquareSingleReverseTenPowNineHighPrefixStdErrorEnvelope_nonneg`,
	  `inverseSquareSingleReverseTenPowNineHighPrefix_abs_error_le_stdErrorEnvelope`,
	  and
	  `inverseSquareSingleReverseTenPowNineHighPrefixState_abs_error_le_stdErrorEnvelope`.
	  These compose the local standard-model errors into one recursive block
	  envelope and prove that the final rounded high-prefix state differs from the
	  exact high-prefix mass by at most that envelope. Coarse-route guard:
	  `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowMarginShiftedLowerBound_lt_coarseAccumulatedStdError`
	  and
	  `inverseSquareSingleReverseTenPowNineHighPrefix_coarseAccumulatedStdErrorGuard_not_sufficient`
	  prove that multiplying the uniform coarse per-step bound across the whole
	  high-prefix length already exceeds the explicit candidate-window margin.
	  Strict finite-cell margin follow-up: added
	  `inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound`,
	  its nonnegativity theorem, the comparison
	  `inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound_le_cellGuardMarginShiftedLowerBound`,
	  the strict comparison
	  `inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound_lt_cellGuardMarginShiftedLowerBound`,
	  the target
	  `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget`,
	  the bridges
	  `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget_of_candidateWindowMarginTarget`,
	  `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuard_of_abs_error_lt_cellGuardMarginShiftedLowerBound`,
	  `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_abs_error_lt_cellGuardMarginShiftedLowerBound`,
	  the candidate consistency theorem
	  `inverseSquareSingleReverseTenPowNineHighPrefixCandidate_abs_error_lt_cellGuardMarginShiftedLowerBound`,
	  and the final wrapper
	  `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_cellGuardMarginTarget_closed`.
	  The remaining D1 proof can now target a single strict absolute-error bound
	  against the larger predecessor/successor-cell margin for the actual rounded
	  high-prefix trace, not a coarse accumulated-envelope comparison and not
	  prefix-step enumeration.
	  Exact-prefix finite-cell follow-up: added
	  `inverseSquareExactReverseTenPowNineHighPrefix_mem_candidateWindowCellGuard`,
	  `inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound_pos`,
	  and
	  `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget_of_eq_exact`.
	  These prove the exact high-prefix mass is strictly inside the finite-cell
	  guard, the strict-cell margin is nonzero, and equality with the exact mass
	  would discharge the strict target. This is still a single high-prefix
	  certificate route, not a low-index suffix enumeration.
- 2026-06-14 focused §1.12.3 reverse high-prefix standard-envelope D1 bridge:
  added
  `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowMarginTarget_of_stdErrorEnvelope_le`,
  `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget_of_stdErrorEnvelope_lt`,
  `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_stdErrorEnvelope_le_candidateWindowMargin`,
  `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_stdErrorEnvelope_lt_cellGuardMargin`,
  `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_stdErrorEnvelope_le_candidateWindowMargin_closed`,
  and
  `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_stdErrorEnvelope_lt_cellGuardMargin_closed`.
  These prove that a genuinely sharp bound on the already-defined recursive
  high-prefix standard-model envelope would discharge the closed-window or
  strict finite-cell D1 target and hence Higham's printed reverse accumulator
  through the already closed suffix route. This does not close D1: the known
  coarse accumulated envelope is still recorded as insufficient, so the
  remaining work is a sharper whole-prefix envelope/cell certificate.
  Validation: `lake build
  LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation` passed. A
  focused `#check` file importing
  `LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation` recognizes all
  six new declarations, and the focused axiom audit for the four theorem
  surfaces reports `[propext, Classical.choice, Quot.sound]`. The aggregate
  `lake env lean examples/LibraryLookup.lean` initially failed because the
  pre-existing imported module `LeanFpAnalysis.FP.Analysis.Problem2_10` had no
  built `.olean`; after rebuilding that dependency with
  `lake build LeanFpAnalysis.FP.Analysis.Problem2_10`, the aggregate lookup
  passed with output redirected to
  `/private/tmp/librarylookup-ch1-reverse-std-envelope.out` and `59440`
  output lines. The touched-file placeholder and trailing-whitespace scans
  returned no matches, and `git diff --check` reported no whitespace errors on
  the touched Lean, lookup, and ledger files.
- 2026-06-13 focused §1.16 Table 1.3 displayed-data layer: added
  `hessenbergDetExampleTable13ComputedSolution`,
  `hessenbergDetExampleTable13SolutionRelativeError`,
  `hessenbergDetExampleTable13ExactDetDisplay`,
  `hessenbergDetExampleTable13ComputedDetDisplay`,
  `hessenbergDetExampleTable13DetRelativeError`, and the theorem block
  `hessenbergDetExampleTable13_computedSolution_rows`,
  `hessenbergDetExampleTable13_exactSolution_rows`,
  `hessenbergDetExampleTable13_det_rows`,
  `hessenbergDetExampleTable13_exactSolution_infNorm_eq`,
  `hessenbergDetExampleTable13_solutionError_infNorm_eq`,
  `hessenbergDetExampleTable13_solution_relative_error_eq`,
  `hessenbergDetExampleTable13_first_component_abs_error_gt_one`,
  `hessenbergDetExampleTable13_solution_relative_error_gt_one`, and
  `hessenbergDetExampleTable13_det_relative_error_lt_two_eight`. This closes
  the printed Table 1.3 solution-vector/error and determinant-accuracy
  contrast as exact rational table data, while keeping the primitive-operation
  single-precision GE trace open. Reran
  `lake build LeanFpAnalysis.FP.Analysis.ProblemDependentStability`; it exited
  successfully. Reran `lake env lean examples/LibraryLookup.lean`, with output
  redirected to `/private/tmp/librarylookup-ch1-table13.out`; it exited
  successfully. The focused axiom audit for the nine new theorem declarations
  reports `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 focused §1.16 Table 1.3 displayed residual layer: added
  `hessenbergDetExampleTable13Residual` and the theorem block
  `hessenbergDetExampleTable13_residual_rows`,
  `hessenbergDetExampleTable13_computedSolution_infNorm_eq`,
  `hessenbergDetExampleTable13_residual_infNorm_eq`,
  `hessenbergDetExampleTable13_scaled_residual_eq`, and
  `hessenbergDetExampleTable13_scaled_residual_gt_one_tenth`. This proves that
  the displayed computed solution, inserted into the exact source system, has
  residual rows `[-1.3842e-7,-1.3842,0,0]`, infinity norm `1.3842`, and
  source-scaled residual `6921/47684 > 0.1`, while keeping the
  primitive-operation single-precision GE trace open. Reran
  `lake build LeanFpAnalysis.FP.Analysis.ProblemDependentStability`; it exited
	  successfully. Reran `lake env lean examples/LibraryLookup.lean`, with output
	  redirected to `/private/tmp/librarylookup-ch1-table13-residual.out`; it
	  exited successfully. The focused axiom audit for the five new theorem
	  declarations reports `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 focused §1.16 Table 1.3 binary32 input-storage layer: added
  `hessenbergDetExampleTable13IeeeSingleFormat`,
  `hessenbergDetExampleTable13SourceAlpha`,
  `hessenbergDetExampleTable13StoredAlpha`,
  `hessenbergDetExampleTable13StoredMatrix`,
  `hessenbergDetExampleTable13StoredRhs`, the finite-system/rounding facts
  `hessenbergDetExampleTable13IeeeSingle_one_finiteSystem`,
  `hessenbergDetExampleTable13IeeeSingle_two_finiteSystem`,
  `hessenbergDetExampleTable13IeeeSingle_round_zero`,
  `hessenbergDetExampleTable13IeeeSingle_round_one`,
  `hessenbergDetExampleTable13IeeeSingle_round_neg_one`,
  `hessenbergDetExampleTable13IeeeSingle_round_two`,
  `hessenbergDetExampleTable13StoredAlpha_finiteSystem`,
  `hessenbergDetExampleTable13StoredAlpha_eq_normalizedValue`,
  `hessenbergDetExampleTable13StoredAlpha_eq`,
  `hessenbergDetExampleTable13StoredAlpha_pos`,
  `hessenbergDetExampleTable13StoredAlpha_ne_zero`,
  `hessenbergDetExampleTable13StoredMatrix_finiteSystem`,
  `hessenbergDetExampleTable13StoredRhs_finiteSystem`, and the input-shape
  theorems `hessenbergDetExampleTable13_storedMatrix_eq_storedAlpha_matrix`
  and `hessenbergDetExampleTable13_storedRhs_rows`, plus the stored-matrix
  facts `hessenbergDetExampleTable13StoredMatrix_isUpperHessenberg`,
  `hessenbergDetExampleTable13StoredMatrix_pivot0_ne_zero`,
  `hessenbergDetExampleTable13StoredMatrix_det_eq`, and
  `hessenbergDetExampleTable13StoredMatrix_det_eq_noPivotUDiag_prod`; the
  first primitive division facts `hessenbergDetExampleTable13_round_one_div_storedAlpha`
  and
  `hessenbergDetExampleTable13StoredMatrix_firstMultiplier_rounds_to_ten_pow_seven`;
  and the first-stage row-update facts
  `hessenbergDetExampleTable13_round_ten_pow_seven_mul_neg_one`,
  `hessenbergDetExampleTable13_round_one_sub_neg_ten_pow_seven`,
  `hessenbergDetExampleTable13_round_neg_one_sub_neg_ten_pow_seven`,
	  `hessenbergDetExampleTable13StoredMatrix_firstStage_diag11_rounds_to`,
	  `hessenbergDetExampleTable13StoredMatrix_firstStage_super12_rounds_to`, and
	  `hessenbergDetExampleTable13StoredMatrix_firstStage_super13_rounds_to`; and
	  the second primitive division facts
	  `hessenbergDetExampleTable13_round_one_div_firstStageDiag_eq_normalizedValue`,
	  `hessenbergDetExampleTable13_round_one_div_firstStageDiag`, and
	  `hessenbergDetExampleTable13StoredMatrix_secondMultiplier_rounds_to`, plus
	  the second-stage product/update facts
	  `hessenbergDetExampleTable13_round_secondMultiplier_mul_firstStageSuper`,
	  `hessenbergDetExampleTable13StoredMatrix_secondStage_diag22_rounds_to`, and
	  `hessenbergDetExampleTable13StoredMatrix_secondStage_super23_rounds_to`, plus
		  the final-elimination facts
		  `hessenbergDetExampleTable13_round_one_div_secondStageDiag`,
		  `hessenbergDetExampleTable13_round_thirdMultiplier_mul_secondStageSuper`, and
		  `hessenbergDetExampleTable13StoredMatrix_finalDiag_rounds_to`, plus the
		  determinant-product facts
		  `hessenbergDetExampleTable13_round_storedAlpha_mul_firstStageDiag`,
		  `hessenbergDetExampleTable13_round_detProduct01_mul_secondStageDiag`,
			  `hessenbergDetExampleTable13_round_detProduct012_mul_finalDiag`,
			  `hessenbergDetExampleTable13_detProduct_leftToRight_rounds_to`,
			  `hessenbergDetExampleTable13_detProduct_relError_eq`, and
			  `hessenbergDetExampleTable13_detProduct_relError_matches_display`, plus the
			  RHS-storage/forward-update facts
			  `hessenbergDetExampleTable13_round_sourceAlpha_sub_three`,
			  `hessenbergDetExampleTable13StoredRhs0_eq_neg_three`,
			  `hessenbergDetExampleTable13StoredRhs_firstStage_rhs1_rounds_to`,
			  `hessenbergDetExampleTable13StoredRhs_secondStage_rhs2_rounds_to`, and
			  `hessenbergDetExampleTable13StoredRhs_finalStage_rhs3_rounds_to`, plus the
			  standard-back-substitution facts
			  `hessenbergDetExampleTable13_standardBackSubSolution_rows` and
			  `hessenbergDetExampleTable13_standardBackSub_first_component_ne_printed`. This
		  closes the primitive input-storage, stored-exact-determinant, first no-pivot
		  multiplier division, first-row update, second no-pivot multiplier division,
		  the next second-stage product/update pair, final no-pivot diagonal, and
		  left-to-right determinant-product adapter without enumerating a GE trace:
		  `fl32(alpha)=14073749/2^47`, the
		  first stored pivot is nonzero, `fl32(1/fl32(alpha))=10^7`,
		  `fl32(1/10000001)=14073747/2^47`, the first row update gives
		  `(10000001,9999999,9999999)`, the next product is `4194303/4194304`, and the
		  `(2,2)`/`(2,3)` updates are `1/4194304` and `-8388607/4194304`; the final
		  multiplier is `4194304`, the final diagonal is `8388608`, and the computed
		  determinant product is `8388609/4194304` with exact relative error
		  `12589/655360065536`, matching the displayed `1.9209e-8` to printed
			  precision; the matrix is the displayed pattern with `alpha` replaced by
			  `fl32(alpha)`, its exact determinant equals the no-pivot diagonal product, the
			  RHS is `[fl32(alpha-3),0,1,2]^T`, `fl32(alpha-3)=-3`, and the forward RHS
			  elimination updates are `30000000`, `-4194303/2097152`, and `8388608`.
			  Standard nearest/even back substitution then gives `[0,1,1,1]^T`, and Lean
			  proves its first component is not the printed `2.3842`. The remaining Table
			  1.3 implementation-facing gap is the hidden arithmetic convention or
			  operation path needed to derive the printed solution row. Reran
  `lake build LeanFpAnalysis.FP.Analysis.ProblemDependentStability`; it exited
		  successfully. Reran `lake env lean examples/LibraryLookup.lean`, with output
			  redirected to `/private/tmp/librarylookup-ch1-table13-backsub-mismatch.out`; it exited
  successfully. The focused axiom audit for the representative new theorem
  declarations reports `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 Table 1.3 adjacent-RHS diagnostic: added
  `hessenbergDetExampleTable13AltStoredRhs0`,
  `hessenbergDetExampleTable13AltStoredRhs0_finiteSystem`,
  `hessenbergDetExampleTable13AltStoredRhs0_gt_neg_three`,
  `hessenbergDetExampleTable13AltStoredRhs0_eq_normalizedValue`,
  `hessenbergDetExampleTable13_neg_three_altStoredRhs0_adjacent`,
  `hessenbergDetExampleTable13StoredRhs0_lt_altStoredRhs0`,
  `hessenbergDetExampleTable13StoredRhs0_ne_altStoredRhs0`,
  `hessenbergDetExampleTable13IeeeSingle_altRow0SecondSub_finiteSystem`,
  `hessenbergDetExampleTable13_altRhsBackSub_row0_firstSub_rounds_to`,
  `hessenbergDetExampleTable13_altRhsBackSub_row0_secondSub_rounds_to`,
  `hessenbergDetExampleTable13_altRhsBackSub_row0_thirdSub_rounds_to`,
  `hessenbergDetExampleTable13_altRhsBackSub_row0_div_rounds_to`,
  `hessenbergDetExampleTable13_altRhsBackSub_x0_rounds_to_printed_float`, and
  `hessenbergDetExampleTable13_altRhsBackSub_first_component_matches_printed`.
  These prove that the alternate first RHS value is exactly the immediate
  binary32 neighbor above `-3`, that ordinary nearest/even storage of the source
  RHS gives the strictly lower value `-3`, and that replacing only the first
  stored RHS entry by the adjacent value `-12582911/4194304` makes the same
  standard back-substitution path return `78125/32768`, which prints as the
  Table 1.3 first component `2.3842` to the displayed precision. Reran
  `lake build LeanFpAnalysis.FP.Analysis.ProblemDependentStability`; it exited
  successfully. Reran `lake env lean examples/LibraryLookup.lean`, with output
  redirected to `/private/tmp/librarylookup-ch1-table13-alt-rhs.out`; it exited
  successfully and produced 50392 lines. The focused axiom audit for the new
  alternate-RHS declarations reports `[propext, Classical.choice, Quot.sound]`.
- 2026-06-13 focused hygiene: no `sorry`/`admit`/`axiom`/`unsafe`/`opaque`
  markers in the touched Lean files, no trailing whitespace in the touched
  Chapter 1 files/docs, `git diff --check` is clean for tracked lookup files,
  no-index diff checks are clean for the untracked Chapter 1 ledger and
  `ProblemDependentStability.lean`/`NonrandomRounding.lean`, and the temporary
  Givens count, Hessenberg mixed-stability, Hessenberg entrywise,
  Hessenberg entrywise-bounds, Kahan grid, Kahan rounded-Horner,
  Kahan IEEE-double, Table 1.3, and Table 1.3 residual scratch files were
  removed.
- `lake build`
- `#print axioms` for
  `normwise_forward_from_backward_vec`,
  `relErrorComputedDenom_lower_bound_from_relError`,
  `relErrorComputedDenom_upper_bound_from_relError`,
  `relError_lower_bound_from_computedDenom`,
  `relError_upper_bound_from_computedDenom`,
  `problem_1_1_relError_bounds`,
  `problem_1_2_candidateBelow_consistent`,
  `problem_1_2_candidateBelow_between`,
  `problem_1_2_candidateBelow_integer_part_last_digit_three`,
  `problem_1_2_candidateInteger_consistent`,
  `problem_1_2_candidateInteger_last_digit_four`,
  `problem_1_2_table_does_not_force_last_digit_four`,
  `problem_1_3_sqrt_one_add_sub_one`,
  `problem_1_3_sin_sub_sin`,
  `problem_1_3_sq_sub_sq`,
  `problem_1_3_one_sub_cos_div_sin`,
  `problem_1_3_lawOfCosines_radicand_sub_rewrite`,
  `problem_1_3_lawOfCosines_radicand_halfAngle`,
  `problem_1_3_lawOfCosines_sqrt_halfAngle`,
  `complexFromRealImag_sq_eq_of_components`,
  `complexSqrtStable_nonnegA_components`,
  `complexSqrtStable_nonnegA_sq`,
  `complexSqrtStable_negA_components`,
  `complexSqrtStable_negA_sq`,
  `complexSqrtStable_zero_sq`,
  `problem_1_6_07734_hello`,
  `problem_1_6_38079_globe`,
  `problem_1_6_318808_bobbie`,
  `problem_1_6_35007_loose`,
  `problem_1_6_5773857734_hells_bells`,
  `problem_1_6_3331_ieee`,
  `problem_1_6_5607_logs`,
  `problem_1_6_5607_sq`,
  `problem_1_6_real_sqrt_31438449_eq_5607`,
  `trigCancellationExactScaled_nonneg`,
  `trigCancellationExactScaled_le_half`,
  `trigCancellationExactScaled_lt_half`,
  `trigCancellationExactScaled_pos_of_cos_ne_one`,
  `trigCancellationDirectScaledFromCos_abs_error_le`,
  `sq_abs_error_le_of_abs_sub_le`,
  `trigCancellationRewriteScaledFromSinHalf_abs_error_le`,
  `trigCancellationRewriteScaledFromSinHalf_abs_error_le_direct_cos_bound`,
  `trigCancellationDirectScaled_eq`,
  `trigCancellationDirectScaled_ne_half`,
  `trigCancellationRewriteScaled_eq_half`,
  `flQuadraticDiscriminant_expansion`,
  `flQuadraticDiscriminant_abs_error_le`,
  `flQuadraticDiscriminantAbsErrorBound_nonneg`,
  `flQuadraticDiscriminantAbsErrorBound_eq_poly`,
  `flQuadraticDiscriminantAbsErrorBound_le_of_u_le`,
  `flQuadraticDiscriminantAbsErrorBound_le_of_simulatesHigherPrecision`,
  `flQuadraticDiscriminant_abs_error_le_bound`,
  `flQuadraticDiscriminant_nonneg_of_abs_error_bound_le`,
  `quadraticRootPlus_sub_midpoint_abs_eq`,
  `quadraticRootMinus_sub_midpoint_abs_eq`,
  `quadraticRootSeparation_abs_eq`,
  `quadraticRoots_near_midpoint_of_discriminant_le`,
  `quadraticRoots_near_midpoint_of_discriminant_guard_failure`,
  `flQuadraticRootPlusFromSqrt_rel_error_le_gamma3`,
  `flQuadraticRootMinusFromSqrt_rel_error_le_gamma3`,
  `quadraticRootPlus_sqrt_perturb_eq`,
  `quadraticRootMinus_sqrt_perturb_eq`,
  `quadraticRootPlus_sqrt_perturb_abs_le_of_abs_eps_le`,
  `quadraticRootMinus_sqrt_perturb_abs_le_of_abs_eps_le`,
  `quadraticRootPlus_sqrt_abs_perturb_eq`,
  `quadraticRootMinus_sqrt_abs_perturb_eq`,
  `quadraticRootPlus_sqrt_abs_perturb_abs_le_of_abs_sub_le`,
  `quadraticRootMinus_sqrt_abs_perturb_abs_le_of_abs_sub_le`,
  `flQuadraticRootPlusWithSqrtRelError_abs_error_le`,
  `flQuadraticRootMinusWithSqrtRelError_abs_error_le`,
  `flQuadraticRootPlusFromSqrt_abs_input_error_le`,
  `flQuadraticRootMinusFromSqrt_abs_input_error_le`,
  `abs_sqrt_sub_sqrt_le_sqrt_abs_sub`,
  `quadraticSqrt_abs_error_le_of_discriminant_abs_error`,
  `flQuadraticRootPlusFromSqrt_discriminant_abs_error_le`,
  `flQuadraticRootMinusFromSqrt_discriminant_abs_error_le`,
  `flQuadraticRootPlusRoundedDiscriminantSqrt_abs_error_le`,
  `flQuadraticRootMinusRoundedDiscriminantSqrt_abs_error_le`,
  `flQuadraticRootPlusMixedDiscriminantSqrt_abs_error_le`,
  `flQuadraticRootMinusMixedDiscriminantSqrt_abs_error_le`,
  `flQuadraticRootPlusComputedSqrt_abs_error_le`,
  `flQuadraticRootMinusComputedSqrt_abs_error_le`,
  `flQuadraticRecoveredRootFromOther_rel_error_le_gamma2`,
  `flQuadraticRecoveredRootFromOther_abs_error_le_of_abs_error`,
  `flQuadraticRecoveredRootMinusFromPlus_abs_error_le`,
  `flQuadraticRecoveredRootPlusFromMinus_abs_error_le`,
  `flQuadraticRecoveredRootMinusFromRoundedPlusDiscriminantSqrt_abs_error_le`,
  `flQuadraticRecoveredRootPlusFromRoundedMinusDiscriminantSqrt_abs_error_le`,
  `flQuadraticRootLargeByBSignRoundedDiscriminantSqrt_abs_error_le`,
  `flQuadraticRootSmallByBSignRoundedDiscriminantSqrt_abs_error_le`,
  `flQuadraticRootsByBSignRoundedDiscriminantSqrt_abs_error_le`,
  `quadraticOverflowExample_b_square_single_finiteOverflowRange`,
  `quadraticOverflowExample_b_square_double_finiteNormalRange`,
  `quadraticOverflowExample_four_a_double_finiteNormalRange`,
  `quadraticOverflowExample_four_ac_double_finiteNormalRange`,
  `quadraticOverflowExample_discriminant_double_finiteNormalRange`,
  `quadraticOverflowExample_discriminant_path_double_finiteNormalRange`,
  `quadraticOverflowExample_b_square_double_roundToEvenOp_standardModel`,
  `quadraticOverflowExample_four_a_double_roundToEvenOp_standardModel`,
  `quadraticOverflowExample_four_ac_double_roundToEvenOp_standardModel`,
  `quadraticOverflowExample_discriminant_sub_double_roundToEvenOp_standardModel`,
  `quadraticOverflowExample_b_square_double_ieeeRoundToNearestEvenOpResult_noFlags`,
  `quadraticOverflowExample_four_a_double_ieeeRoundToNearestEvenOpResult_noFlags`,
  `quadraticOverflowExample_four_ac_double_ieeeRoundToNearestEvenOpResult_noFlags`,
  `quadraticOverflowExample_discriminant_sub_double_ieeeRoundToNearestEvenOpResult_noFlags`,
  `quadraticOverflowExample_exact_discriminant_path_double_ieeeRoundToNearestEvenOpResult_noFlags`,
  `quadraticOverflowExample_b_square_doubleRounded`,
  `quadraticOverflowExample_four_a_doubleRounded`,
  `quadraticOverflowExample_four_ac_doubleRounded`,
  `quadraticOverflowExample_discriminant_doubleRounded`,
  `quadraticOverflowExample_four_ac_doubleRounded_finiteNormalRange`,
  `quadraticOverflowExample_discriminant_sub_doubleRounded_finiteNormalRange`,
  `quadraticOverflowExample_discriminant_path_doubleRounded_finiteNormalRange`,
  `quadraticOverflowExample_four_ac_doubleRounded_roundToEvenOp_standardModel`,
  `quadraticOverflowExample_discriminant_sub_doubleRounded_roundToEvenOp_standardModel`,
  `quadraticOverflowExample_discriminant_path_doubleRounded_roundToEvenOp_standardModel`,
  `quadraticOverflowExample_four_ac_doubleRounded_ieeeRoundToNearestEvenOpResult_noFlags`,
  `quadraticOverflowExample_discriminant_sub_doubleRounded_ieeeRoundToNearestEvenOpResult_noFlags`,
  `quadraticOverflowExample_discriminant_path_doubleRounded_ieeeRoundToNearestEvenOpResult_noFlags`,
  `quadraticOverflowExample_discriminant_path_doubleRounded_ieeeRoundToNearestEvenOpResult_toReal`,
  `quadraticOverflowExample_scaled_b_square_single_finiteNormalRange`,
  `quadraticOverflowExample_scaled_four_ac_single_finiteNormalRange`,
  `quadraticOverflowExample_scaled_discriminant_single_finiteNormalRange`,
  `quadraticOverflowExample_roots`,
  `quadraticScaledOverflowExample_roots`,
  `quadraticScaledOverflowExample_variable_scaling`,
  `mullerExact_satisfies_recurrence`,
  `mullerExact_lt_succ`,
  `mullerExact_tendsto_six`,
  `problem_1_8_x34_rounds_to_5_998`,
  `mullerDecimal4Trace_rounding_intervals`,
  `mullerDecimal4Trace_34_eq_100`,
  `mullerDecimal4Trace_34_abs_error_gt_94`,
  `mullerModeY_linear_recurrence`,
  `mullerModeRatio_eq_hundred_sub`,
  `mullerModeRatio_gt_99_of_dominant`,
  `flPrefixMeanTrajectory_abs_error_le_budget`,
  `flPrefixCorrectedSumSquaresTrajectory_abs_error_le_budget`,
  `flSampleVarianceUpdate_abs_error_le_budget`,
  `prefixMean_example_values_10000_10001_10002`,
  `prefixCorrectedSumSquares_example_values_10000_10001_10002`,
  `sampleVarianceUpdate_example_10000_10001_10002`,
  `sampleVarianceOnePassAggregates_cancelled_relError_example_10000_10001_10002`,
  `sampleVarianceOnePassAggregates_neg_of_sumSq_lt`,
  `sampleVarianceOnePassAggregates_negative_example_10000_10001_10002`,
  `sampleVarianceConditionDen_eq_sum_sq_deviation`,
  `sampleVariance_vecNorm2Sq_eq_conditionDen_add_mean_sq`,
  `sampleMean_add_scaled`,
  `sampleVarianceTwoPass_add_scaled_sub_eq`,
  `sampleVarianceDirectionalCoeff_componentwise_le`,
  `sampleVarianceDirectionalCoeff_normwise_le`,
  `flSampleMean_backward_error`,
  `flSampleMean_abs_error_le_gamma`,
  `sampleMean_deviation_sum_eq_zero`,
  `sum_sq_sub_perturbedMean_eq_sum_sq_sub_sampleMean_add`,
  `sampleVarianceTwoPassWithMean_eq_twoPass_add`,
  `sampleVarianceTwoPass_le_twoPassWithMean`,
  `sampleVarianceTwoPassWithMean_relError_eq_quadratic`,
  `sampleVarianceTwoPassWithMean_mul_one_add_relError_le`,
  `exists_weightedRelativeErrorFactor_of_nonneg_sum`,
  `flSquaredDeviationWithMean_eq_mul_one_add_gamma3`,
  `flSampleVarianceTwoPassWithMean_eq_mul_one_add_gamma`,
  `flSampleVarianceTwoPass_relError_le_gamma_add_mean_quadratic`,
  `flSampleVarianceTwoPass_mean_quadratic_le_gamma_sq`,
  `flSampleVarianceTwoPass_relError_le_gamma_add_gamma_sq_mean_bound`,
  `flSampleVarianceTwoPassProblem110MeanQuadraticBound_nonneg`,
  `flSampleVarianceTwoPassProblem110Remainder_nonneg`,
  `gamma_eq_linear_plus_quadratic_remainder`,
  `flSampleVarianceTwoPassProblem110RemainderQuadraticCoeff`,
  `flSampleVarianceTwoPassProblem110RemainderQuadraticBound_eq_coeff_mul_u_sq`,
  `flSampleVarianceTwoPassProblem110Remainder_le_quadratic_bound`,
  `flSampleVarianceTwoPass_relError_le_linear_u_add_explicit_remainder`,
  `flSampleVarianceTwoPass_relError_le_linear_u_add_problem110_remainder`,
  `sampleVarianceKappaNClosed_eq_expanded`,
  `sampleVarianceKappaCClosed_le_KappaNClosed`,
  `expOneApproxRoundedBase_eq_exact_base_mul_initial_error_pow`,
  `expOneApproxLogExpExact_eq_exact_base`,
  `expOneApproxLogExpWithLogRelError_eq_exact_base_mul_exp`,
  `expOneApproxLogExpUnitRoundoffEnvelope`,
  `expOneApproxLogExpUnitRoundoffEnvelope_isBigO`,
  `expOneApproxLogExp_exponentCoeff_nonneg`,
  `expOneApproxLogExp_exponentCoeff_le_one`,
  `expOneApproxLogExp_logRelError_exponent_abs_le`,
  `expOneApproxLogExpRoundedOuter_eq_exact_base_mul_exp_mul`,
  `real_abs_exp_sub_one_le_exp_abs_sub_one`,
  `real_abs_exp_sub_one_le_of_abs_le`,
  `expOneApproxLogExpRoundedOuter_relError_le_exp_mul`,
  `expOneApproxLogExpRoundedOuter_relError_le_fp`,
  `expOneApproxLogExpFiniteRoundToEven`,
  `expOneApproxLogExpFiniteRoundToEven_exists_contract_of_finiteNormalRange`,
  `expOneApproxLogExpFiniteRoundToEven_relError_le_fp_of_finiteNormalRange`,
  `noPivotExample_kappaInf_eq`,
  `noPivotRoundedLU_error_matrix`,
  `noPivotIeeeSingle_add_one_inv_epsilon_rounds_to_inv`,
  `noPivotIeeeSingle_add_one_normalized_exp26_rounds_to_self`,
  `noPivotIeeeSingle_add_one_inv_rounds_to_inv_of_inv_normalized_exp26`,
  `noPivotIeeeSingle_add_one_normalized_rounds_to_self_of_two_lt_ulp`,
  `noPivotIeeeSingle_add_one_normalized_rounds_to_self_of_exp_ge_26`,
  `noPivotIeeeSingle_add_one_inv_rounds_to_inv_of_inv_normalized_exp_ge_26`,
  `noPivotIeeeSingle_add_one_normalized_rounds_to_self_of_ulp_eq_two_even`,
  `noPivotIeeeSingle_add_one_normalized_rounds_to_succ_of_ulp_eq_two_odd`,
  `noPivotIeeeSingle_add_one_normalized_exp25_even_rounds_to_self`,
  `noPivotIeeeSingle_add_one_normalized_exp25_odd_rounds_to_succ`,
  `noPivotIeeeSingle_add_one_inv_rounds_to_inv_of_inv_normalized_exp25_even`,
  `noPivotIeeeSingle_add_one_inv_rounds_to_succ_of_inv_normalized_exp25_odd`,
  `noPivotIeeeSingle_add_one_normalized_exp25_max_rounds_to_exp26_min`,
  `noPivotIeeeSingle_add_one_inv_rounds_to_exp26_min_of_inv_normalized_exp25_max`,
  `noPivotIeeeSingle_add_one_normalized_rounds_to_self_of_left_rounding_cases`,
  `noPivotIeeeSingle_add_one_inv_rounds_to_inv_of_inv_normalized_left_rounding_cases`,
  `noPivotIeeeSingle_add_one_inv_rounds_to_inv_requires_inv_finiteSystem`,
  `noPivotIeeeSingle_add_one_inv_not_rounds_to_inv_of_inv_not_finiteSystem`,
  `noPivotIeeeSingleSmallEpsilon_error_matrix`,
  `noPivotPartialPivotLUFactSpec`,
  `noPivotPartialPivotLUBackwardError_zero`,
  `noPivotIeeeSingleSmallEpsilon_finiteSystem`,
  `noPivotIeeeSingle_partialPivot_div_epsilon_one_rounds_to_epsilon`,
  `noPivotIeeeSingle_partialPivot_mul_epsilon_one_rounds_to_epsilon`,
  `noPivotIeeeSingle_add_one_epsilon_rounds_to_one`,
  `noPivotIeeeSingle_partialPivot_sub_neg_one_epsilon_rounds_to_neg_one`,
  `noPivotIeeeSingle_partialPivot_div_epsilon_one_rounds_to_epsilon_of_finiteSystem`,
  `noPivotIeeeSingle_partialPivot_mul_epsilon_one_rounds_to_epsilon_of_finiteSystem`,
  `noPivotIeeeSingle_add_one_epsilon_rounds_to_one_of_nonneg_le_small`,
  `noPivotIeeeSingle_partialPivot_sub_neg_one_epsilon_rounds_to_neg_one_of_nonneg_le_small`,
  `noPivotIeeeSinglePartialPivotRoundedLUBackwardError`,
  `noPivotPartialPivotPrimitiveRoundedU_eq_roundedU_of_rounds`,
  `noPivotPartialPivotRoundedLUBackwardError`,
  `noPivotPartialPivotPrimitiveRoundedLUBackwardError_of_rounds`,
  `noPivotPartialPivot_multiplier_abs_le_one`,
  `noPivotPartialPivotU_diag_nonzero`,
  `repeatedSquare_repeatedSqrt_sixty_eq_self`,
  `hp48gTwelveDigitBelowOne`,
  `Hp48gSqrtSquareSurrogateLaws`,
  `hp48gSqrtSquareTrace`,
  `hp48gSqrtSquareTrace_eq_surrogate_of_laws`,
  `hp48gSqrtSquareSurrogate_relError_100`,
  `hp48gSqrtSquareSurrogate_absError_of_ge_one`,
  `hp48gSqrtSquareSurrogate_relError_of_ge_one`,
  `hp48gSqrtSquareSurrogate_absError_of_nonneg_lt_one`,
  `hp48gSqrtSquareSurrogate_relError_of_pos_lt_one`,
  `inverseSquareTerm_le_two_pow_neg_24_of_ge`,
  `inverseSquareTerm_between_half_ulp_and_one_ulp_of_ge_2897_lt_4096`,
  `inverseSquareSingle_add_term_rounds_to_next_of_half_ulp_lt`,
  `inverseSquareSingle_add_term_rounds_to_next_of_index_range`,
  `inverseSquareSingleEarlyMantissaPrefix_2895_eq`,
  `inverseSquareSingleEarlyMantissaPrefix_2895_add_base_eq_preWindow`,
  `inverseSquareSingleEarlyMantissaIncrementNearestCertificateBool_eq_true`,
  `inverseSquareSingleEarlyMantissaIncrementNearestCertificate`,
  `inverseSquareSingle_add_term_rounds_to_nearest_mantissa_of_scaled_bounds`,
  `inverseSquareSingleForwardAccumulator_one_eq_one`,
  `inverseSquareSingleForwardAccumulator_2896_eq_prePlateauWindowStart_of_early_mantissa_increment_rule`,
  `inverseSquareSingleEarlyMantissaIncrementRule_closed`,
  `inverseSquareSingleForwardAccumulator_2896_eq_prePlateauWindowStart`,
  `inverseSquareSingleForwardAccumulatorFrom_normalizedValue_of_index_window`,
  `inverseSquareSingleForwardAccumulatorFrom_prePlateauWindowStart_2897_of_le_1194`,
  `inverseSquareSingleForwardAccumulatorFrom_prePlateauWindowStart_2897_1194_eq_sixBeforePlateau`,
  `inverseSquareSingleForwardAccumulatorFrom_sixBeforePlateau_4091_of_le_5`,
  `inverseSquareSingleForwardAccumulatorFrom_prePlateauWindowStart_2897_lt_plateau_of_lt_1200`,
  `inverseSquareSingleForwardAccumulatorFrom_sixBeforePlateau_4091_six_add_eq_plateau`,
  `inverseSquareSingleForwardAccumulatorFrom_prePlateauWindowStart_2897_1200_add_eq_plateau`,
  `inverseSquareSingleForwardAccumulator_2896_add_lt_plateau_of_2896_eq_prePlateauWindowStart`,
  `inverseSquareSingleForwardAccumulator_4096_add_eq_plateau_of_2896_eq_prePlateauWindowStart`,
  `inverseSquareSingleForwardAccumulator_2896_add_lt_plateau_of_early_mantissa_increment_rule`,
  `inverseSquareSingleForwardAccumulator_4096_add_eq_plateau_of_early_mantissa_increment_rule`,
  `inverseSquareSingleForwardAccumulator_2896_add_lt_plateau`,
  `inverseSquareSingleForwardAccumulator_4096_add_eq_plateau`,
  `inverseSquareSingleReverseAccumulatorFrom_add`,
  `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq`,
  `inverseSquareSingleReverseAccumulator_split`,
  `inverseSquareSingleReverseAccumulator_ten_pow_nine_split_4096`,
  `inverseSquareReverseTenPowNineHighPrefix_index_ge_4097`,
  `inverseSquareTerm_le_two_pow_neg_24_of_reverse_ten_pow_nine_high_prefix`,
  `inverseSquareExactReverseAccumulatorFrom_add_start`,
  `inverseSquareExactReverseAccumulatorFrom_add`,
  `inverseSquareExactReverseAccumulator_split`,
  `inverseSquareExactReverseAccumulator_ten_pow_nine_split_4096`,
  `inverseSquareExactReverseAccumulator_ten_pow_nine_eq_highPrefix_add_low4096`,
  `inverseSquareTerm_le_telescope`,
  `inverseSquareExactReverseAccumulatorFrom_le_telescope`,
  `inverseSquareExactReverseTenPowNineHighPrefix_le_inv_4096`,
  `inverseSquareExactReverseAccumulator_ten_pow_nine_sub_low4096_le_inv_4096`,
  `inverseSquareSingleSixBeforePlateau_add_4091_term_rounds_to_fiveBeforePlateau`,
  `inverseSquareSingleFiveBeforePlateau_add_4092_term_rounds_to_fourBeforePlateau`,
  `inverseSquareSingleFourBeforePlateau_add_4093_term_rounds_to_threeBeforePlateau`,
  `inverseSquareSingleThreeBeforePlateau_add_4094_term_rounds_to_twoBeforePlateau`,
  `inverseSquareSingleTwoBeforePlateau_add_4095_term_rounds_to_prePlateau`,
  `inverseSquareSinglePrePlateau_add_4096_term_rounds_to_plateau`,
  `inverseSquareSinglePlateau_add_4096_term_rounds_to_self`,
  `inverseSquareSinglePlateau_add_positive_term_le_two_pow_neg_24_rounds_to_self`,
  `inverseSquareSinglePlateau_add_term_rounds_to_self_of_ge_4096`,
  `increasingPrecisionSinExampleSource_perturbation_abs_le`,
  `increasingPrecisionSinExampleSource_ieeeSingle_roundToEven_one`,
  `increasingPrecision_ieeeSingle_roundToEven_one_seventh`,
  `increasingPrecision_ieeeDouble_roundToEven_one_seventh`,
  `increasingPrecision_ieeeSingle_roundToEven_one_seventh_error`,
  `increasingPrecision_ieeeDouble_roundToEven_one_seventh_error`,
  `increasingPrecision_one_seventh_binary_grid_abs_error_ge`,
  `increasingPrecision_one_seventh_binary_grid_abs_error_gt_scale_of_t_le_twenty`,
  `increasingPrecision_one_seventh_binary_grid_abs_error_gt_scale_of_t_le_twenty_three`,
  `increasingPrecision_one_seventh_binary_grid_lower_bound_lt_scale_at_twenty_four`,
  `increasingPrecisionSinExampleSource_perturbation_lt_one_seventh_binary_grid_error_of_t_le_twenty`,
  `increasingPrecisionSinExampleSource_perturbation_lt_one_seventh_binary_grid_error_of_t_le_twenty_three`,
  `seven_not_dvd_two_pow_nat`, `one_seventh_not_binaryTerminating`,
  `one_seventh_not_ieeeSingleFiniteSystem`,
  `one_seventh_not_ieeeDoubleFiniteSystem`,
  `increasingPrecisionExampleElse_relError_one_of_expHat_one`, `increasingPrecisionExampleElse_two_precision_failure_of_expHat_one`,
  `expm1Algorithm2Exact_eq_algorithm1Exact`,
  `expm1LogRatio_tendsto_one`,
  `expm1Log_one_add_sub_linear_quadratic_abs_le`,
  `expm1LogRatioDenRemainder_abs_le`,
  `expm1LogRatio_one_add_eq_inv_one_sub_half_add_remainder`,
  `expm1LogRatio_one_add_sub_one_add_half_abs_le`,
  `expm1LogRatio_one_add_diff_sub_half_abs_le`,
  `expm1LogRatio_abs_ge_one_sub_radius_bound`,
  `expm1LogRatio_abs_ge_half_of_radius`,
  `expm1LogRatio_mul_one_add_delta_diff_sub_y_delta_half_abs_le`,
  `expm1LogRatio_mul_one_add_delta_diff_sub_delta_half_abs_le`,
  `expm1Algorithm2RoundedCore_eq_source_1_9`,
  `expm1Algorithm2RoundedCore_eq_source_1_9_of_exact_sub`,
  `expm1Algorithm2RoundedCore_eq_source_1_9_of_guardDigitSubtractionModel`,
  `expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_ferguson`,
  `expm1Algorithm2_yhat_one_sterbenzRatioCondition_of_abs_sub_one_le_third`,
  `expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_sterbenz_radius`,
  `expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_exp_perturb_sterbenz_radius`,
  `expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_exp_x_sterbenz_radius`,
  `expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_exp_x_mul_one_add_u_sterbenz`,
  `expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_exact_sub`,
  `expm1Algorithm2RoundedCore_relError_le_gamma2_of_exact_sub`,
  `expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_sterbenz_radius`,
  `expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_perturb_sterbenz_radius`,
  `expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_x_sterbenz_radius`,
  `expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_x_mul_one_add_u_sterbenz`,
  `expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_finiteRoundToEven_exp_x_mul_one_add_u_sterbenz`,
  `expm1Algorithm2RoundedCore_relError_le_gamma2_of_finiteRoundToEven_exp_x_mul_one_add_u_sterbenz`,
  `FloatingPointFormat.finiteRoundToEven_finiteSystem`,
  `FloatingPointFormat.finiteRoundToEvenOp_finiteSystem`,
  `FloatingPointFormat.finiteRoundToEvenSqrt_finiteSystem`,
  `expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_rounded_exp_x_mul_one_add_u_sterbenz`,
  `expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_finiteRoundToEven_rounded_exp_x_mul_one_add_u_sterbenz`,
  `expm1Algorithm2RoundedCore_relError_le_gamma2_of_finiteRoundToEven_rounded_exp_x_mul_one_add_u_sterbenz`,
  `expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma4`,
  `expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma3`,
  `expm1Algorithm2RoundedCore_relError_le_gamma4`,
  `expm1Algorithm2RoundedCore_relError_le_gamma3`,
  `expm1Algorithm2RoundedCore_relError_le_local_bound`,
  `expm1Algorithm2RoundedCore_relError_le_local_bound_gamma3`,
  `expm1Algorithm2LocalRelErrorBound_le_eta_add_gamma4`,
  `expm1Algorithm2RoundedCore_relError_le_eta_add_gamma4`,
  `expm1Algorithm2RoundedCore_relError_le_eta_add_gamma3`,
  `expm1Algorithm2SlowRatioPerturbationBound_le_of_abs_bounds`,
  `expm1Algorithm2LocalDrift_le_primitive_bound`,
  `expm1Algorithm2PrimitiveSlowRemainderBound`,
  `expm1Algorithm2PrimitiveDriftBound_le_half_u_mul_abs_logRatio_add_slow_remainder`,
  `expm1Algorithm2RoundedCore_relError_le_eta_add_gamma4_of_primitive_bounds`,
  `expm1Algorithm2RoundedCore_relError_le_eta_add_gamma3_of_primitive_bounds`,
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_remainder`,
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_remainder_of_primitive_bounds`,
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_local_remainder_of_abs_bounds`,
  `expm1Algorithm2PrimitiveSlowRemainderBound_le_of_radius`,
  `expm1Algorithm2_yhat_sub_one_abs_le_of_y_radius`,
  `expm1Algorithm2_exp_sub_one_abs_le_of_abs_x_le`,
  `expm1LogRatio_exp_ne_zero_of_ne_zero`,
  `expm1Algorithm2_exp_x_combined_radius_le_third_of_exp_mul_one_add_u_le`,
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_radius_remainder_of_abs_bounds`,
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_radius_bound_of_abs_bounds`,
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_perturb_radius_bound`,
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_x_radius_bound`,
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_x_mul_one_add_u_bound`,
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_u_radius_bound_of_abs_bounds`,
  `expm1Algorithm2ThreePointFiveUnitBound`,
  `expm1Algorithm2Gamma3Scalar`,
  `expm1Algorithm2ThreePointFiveUnitBoundScalar`,
  `expm1Algorithm2ThreePointFiveUnitBound_eq_scalar`,
  `expm1Algorithm2ThreePointFiveUnitBoundScalar_isBigO`,
  `expm1Algorithm2ThreePointFiveUnitBound_eq_zero_of_u_eq_zero`,
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_u_radius_bound_of_unit_bounds`,
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_unit_bound_of_unit_bounds`,
  `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_normalized_remainder_of_abs_bounds`,
  `givensRotation_mulVec_p`,
  `givensRotation_mulVec_q`,
  `givensRotation_ratio_zeroes_q`,
  `givensRotation_ratio_mulVec_p`,
  `givensRotation_trig_orthogonal`,
  `beneficialPowerCharDet_eq`,
  `beneficialPowerCharDet_root_zero`,
  `beneficialPowerCharDet_root_small`,
  `beneficialPowerCharDet_root_dominant`,
  `beneficialPowerEigenvalueSmall_display_accuracy`,
  `beneficialPowerEigenvalueDominant_display_accuracy`,
  `beneficialPowerStart_isRightEigenpair_zero`,
  `beneficialPowerFirstStep_zero`,
  `beneficialPowerShiftedMatrix_mul_start`,
  `beneficialPower_inverseIteration_shiftedSystem_solution_start`,
  `beneficialPower_shiftedInverse_mul_start_of_leftInverse`,
  `powerMethodStep_add_matrix`,
  `beneficialPowerFirstStep_perturbed_eq_delta`,
  `beneficialPowerFirstStep_perturbed_nonzero_of_delta_row_sum_ne_zero`,
  `hessenbergDiagRoundedStep_eq_perturbed_exactStep`,
  `hessenbergEntrywisePerturbation_diag`,
  `hessenbergEntrywisePerturbation_subdiag`,
  `hessenbergSubdiagPerturbationFactors_prod`,
  `hessenbergEntrywisePerturbation_isUpperHessenberg`,
  `hessenbergEntrywisePerturbation_diag_signedRelErrorWitness`,
  `hessenbergEntrywisePerturbation_diag_abs_error_le`,
  `hessenbergEntrywisePerturbation_subdiag_signedRelErrorWitness_exists`,
  `hessenbergEntrywisePerturbation_subdiag_abs_error_le_gamma`,
  `hessenbergEntrywisePerturbation_abs_error_le_gamma_three`,
  `hessenbergDiagRoundedStep_eq_entrywisePerturbedExactStep`,
  `hessenbergDetRoundedProduct_signedRelError`,
  `hessenbergDetRoundedProduct_relError_eq`,
  `hessenbergDetRoundedProduct_relError_le_gamma`,
  `hessenbergDetRoundedProduct_relError_le_gamma_of_det_eq_diag_prod`,
  `hessenbergDetExample_mul_ones`,
  `hessenbergDetExampleMatrixInv_alpha_ten_pow_isInverse`,
  `hessenbergDetExampleMatrix_alpha_ten_pow_infNorm_eq`,
  `hessenbergDetExampleMatrixInv_alpha_ten_pow_infNorm_eq`,
  `hessenbergDetExample_kappaInfProduct_alpha_ten_pow_eq`,
  `hessenbergDetExample_kappaInfProduct_alpha_ten_pow_near_sixteen`,
  `hessenbergDetExampleNoPivotU_blockTriangular`,
  `hessenbergDetExampleNoPivotU_det_eq_diag_prod`,
  `hessenbergDetExampleNoPivotUDiag_prod_eq`,
  `hessenbergDetExampleMatrix_det_eq_noPivotUDiag_prod`,
  `hessenbergDetExampleMatrix_det_eq`,
  `hessenbergDetExampleRoundedProduct_relError_le_gamma`,
  `hessenbergDetExampleMatrix_alpha_ten_pow_det_eq`,
  `hessenbergDetExampleMatrix_alpha_ten_pow_det_near_two`,
  `hessenbergDetExample_alpha_ten_pow_exact_table_baseline`,
  `hessenbergDetExampleTable13_computedSolution_rows`,
  `hessenbergDetExampleTable13_exactSolution_rows`,
  `hessenbergDetExampleTable13_det_rows`,
  `hessenbergDetExampleTable13_exactSolution_infNorm_eq`,
  `hessenbergDetExampleTable13_solutionError_infNorm_eq`,
  `hessenbergDetExampleTable13_solution_relative_error_eq`,
  `hessenbergDetExampleTable13_first_component_abs_error_gt_one`,
  `hessenbergDetExampleTable13_solution_relative_error_gt_one`,
  `hessenbergDetExampleTable13_det_relative_error_lt_two_eight`,
  `hessenbergDetExampleTable13_residual_rows`,
  `hessenbergDetExampleTable13_computedSolution_infNorm_eq`,
  `hessenbergDetExampleTable13_residual_infNorm_eq`,
  `hessenbergDetExampleTable13_scaled_residual_eq`,
  `hessenbergDetExampleTable13_scaled_residual_gt_one_tenth`,
  `hessenbergDetExample_alpha_ten_pow_roundedProduct_relError_le_gamma`,
  `hessenbergDetExampleFirstMultiplier_alpha_ten_pow`,
  `kahanHornerNumerator_eq_poly`,
  `kahanHornerDenominator_eq_poly`,
  `kahanHornerNumerator_shifted_eq`,
  `kahanHornerDenominator_shifted_eq`,
  `kahanHornerGridPoint_succ_sub`,
  `kahanHornerGridPoint_mem_source_interval`,
  `kahanHornerGridPoint_pairwise_distance_le_source_width`,
  `kahanHornerDenominator_grid_one_pos`,
  `kahanHornerDenominator_gt_three_on_source_grid_interval`,
  `kahanHornerDenominator_pos_on_source_grid_interval`,
  `kahanHornerDenominator_grid_pos_of_one_le_of_le_three_sixty_one`,
  `kahanRationalFunctionFirstDiffKernel_abs_lt_one`,
  `kahanRationalFunction_first_diff_num_factor`,
  `kahanRationalFunction_source_interval_variation_from_first_lt`,
  `kahanRationalFunction_grid_variation_from_first_lt`,
  `kahanRationalFunction_grid_pair_variation_lt_two`,
  `flKahanHornerNumerator_eq_errorEval`,
  `flKahanHornerDenominator_eq_errorEval`,
  `flKahanRationalFunction_eq_errorEval`,
  `ieeeDoubleKahanHornerNumerator_eq_errorEval_of_finiteNormal`,
  `ieeeDoubleKahanHornerDenominator_eq_errorEval_of_finiteNormal`,
  `ieeeDoubleKahanRationalFunction_eq_errorEval_of_finiteNormal`,
  `kahanRationalFunction_first_to_last_variation_lt`,
  `kahanRoundedGrid_endpoint_error_spread_gt_of_output_spread`,
  `ieeeDoubleKahanRationalFunction_endpoint_error_spread_gt_of_output_spread`,
  `kahanRationalFunction_grid_175_289_variation_lt_one_e15`,
  `kahanRoundedGrid_175_289_error_spread_gt_of_output_spread`,
  `ieeeDoubleKahanRationalFunction_175_289_error_spread_gt_of_output_spread`,
  `ieeeDoubleKahanStoredGridPoint`,
  `ieeeDoubleKahanStoredGridRationalFunction`,
  `ieeeDoubleKahanStoredGridPoint_175_eq`,
  `ieeeDoubleKahanStoredGridPoint_289_eq`,
  `ieeeDoubleKahanStoredGridNumerator_m0_175_eq`,
  `ieeeDoubleKahanStoredGridNumerator_m0_289_eq`,
  `ieeeDoubleKahanStoredGridNumerator_s0_175_eq`,
  `ieeeDoubleKahanStoredGridNumerator_s0_289_eq`,
  `ieeeDoubleKahanStoredGridNumerator_m1_175_eq`,
  `ieeeDoubleKahanStoredGridNumerator_m1_289_eq`,
  `ieeeDoubleKahanStoredGridNumerator_s1_175_eq`,
  `ieeeDoubleKahanStoredGridNumerator_s1_289_eq`,
  `ieeeDoubleKahanStoredGridNumerator_m2_175_eq`,
  `ieeeDoubleKahanStoredGridNumerator_m2_289_eq`,
  `ieeeDoubleKahanStoredGridNumerator_s2_175_eq`,
  `ieeeDoubleKahanStoredGridNumerator_s2_289_eq`,
  `ieeeDoubleKahanStoredGridNumerator_m3_175_eq`,
  `ieeeDoubleKahanStoredGridNumerator_m3_289_eq`,
  `ieeeDoubleKahanStoredGridHornerNumerator_175_eq`,
  `ieeeDoubleKahanStoredGridHornerNumerator_289_eq`,
  `ieeeDoubleKahanStoredGridDenominator_s0_175_eq`,
  `ieeeDoubleKahanStoredGridDenominator_s0_289_eq`,
  `ieeeDoubleKahanStoredGridDenominator_m1_175_eq`,
  `ieeeDoubleKahanStoredGridDenominator_m1_289_eq`,
  `ieeeDoubleKahanStoredGridDenominator_s1_175_eq`,
  `ieeeDoubleKahanStoredGridDenominator_s1_289_eq`,
  `ieeeDoubleKahanStoredGridDenominator_m2_175_eq`,
  `ieeeDoubleKahanStoredGridDenominator_m2_289_eq`,
  `ieeeDoubleKahanStoredGridDenominator_s2_175_eq`,
  `ieeeDoubleKahanStoredGridDenominator_s2_289_eq`,
  `ieeeDoubleKahanStoredGridDenominator_m3_175_eq`,
  `ieeeDoubleKahanStoredGridDenominator_m3_289_eq`,
  `ieeeDoubleKahanStoredGridHornerDenominator_175_eq`,
  `ieeeDoubleKahanStoredGridHornerDenominator_289_eq`,
  `ieeeDoubleKahanStoredGridRationalFunction_175_eq`,
  `ieeeDoubleKahanStoredGridRationalFunction_289_eq`,
  `ieeeDoubleKahanStoredGridRationalFunction_175_289_error_spread_gt_of_output_spread`,
  `ieeeDoubleKahanStoredGridRationalFunction_175_289_error_spread_gt_one_e13_of_output_values`,
  `ieeeDoubleKahanStoredGridRationalFunction_175_289_error_spread_gt_one_e13`,
  `exists_ieeeDoubleKahanStoredGridRationalFunction_grid_error_spread_gt_one_e13`,
  `relativeResidual2_le_of_relativeMatrixOnlyBackwardError2Le`,
  `opNorm2Le_of_sqrt_two_infNorm_le`,
  `gepp2_relativeResidual2_le_wilkinson`,
  `cramer2x2NumeratorAbsTerms_div_det_eq_invAbsRhs_inverse`,
  `cramer2x2Solution_error_from_flNumerators_exact_den_invAbsRhs`,
  `cramer2x2Solution_relative_forward_error_from_flNumerators_exact_den_condAt`,
  and `cramer2x2Residual_infNorm_from_flNumerators_exact_den_condInv`;
  each reports only `[propext, Classical.choice, Quot.sound]`.
- `rg -n "\b(sorry|admit)\b|(^|[^A-Za-z])axiom([^A-Za-z]|$)|\bunsafe\b|\bopaque\b" LeanFpAnalysis/FP/Analysis/Accumulation.lean LeanFpAnalysis/FP/Analysis/BeneficialRounding.lean LeanFpAnalysis/FP/Analysis/CalculatorWords.lean LeanFpAnalysis/FP/Analysis/CancellationOfRoundingErrors.lean LeanFpAnalysis/FP/Analysis/ComplexSqrt.lean LeanFpAnalysis/FP/Analysis/Error.lean LeanFpAnalysis/FP/Analysis/IncreasingPrecision.lean LeanFpAnalysis/FP/Analysis/InstabilityWithoutCancellation.lean LeanFpAnalysis/FP/Analysis/NearInteger.lean LeanFpAnalysis/FP/Analysis/NonrandomRounding.lean LeanFpAnalysis/FP/Analysis/ProblemDependentStability.lean LeanFpAnalysis/FP/Analysis/Stability.lean LeanFpAnalysis/FP/Analysis/TrigCancellation.lean LeanFpAnalysis/FP/Analysis/Quadratic.lean LeanFpAnalysis/FP/Analysis/MullerRecurrence.lean LeanFpAnalysis/FP/Analysis/SampleVariance.lean LeanFpAnalysis/FP/Analysis/CramersRule.lean LeanFpAnalysis/FP/Analysis/PerturbationTheory.lean LeanFpAnalysis/FP/Analysis/MatrixAlgebra.lean LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean LeanFpAnalysis/FP/Algorithms/QR/GivensSpec.lean examples/LibraryLookup.lean`

- 2026-06-13 focused §1.9 aggregate-negative witness pass:
  `lake build LeanFpAnalysis.FP.Analysis.SampleVariance` succeeded, and
  `lake env lean examples/LibraryLookup.lean >
  /private/tmp/librarylookup-ch1-samplevariance-negative.out` succeeded. The
  focused Lean placeholder scan on
  `LeanFpAnalysis/FP/Analysis/SampleVariance.lean` and
  `examples/LibraryLookup.lean` returned no matches. `git diff --check --`
  for the touched tracked docs/lookup files succeeded. The focused axiom audit
  for `sampleVarianceOnePassAggregates_negative_lt_zero_example_10000_10001_10002`,
  `sampleVarianceOnePassAggregates_negative_absError_example_10000_10001_10002`,
  and `sampleVarianceOnePassAggregates_negative_relError_example_10000_10001_10002`
  reports only `[propext, Classical.choice, Quot.sound]`. A broader docs scan
  still sees historical prose about prior "axiom audit" entries; that is not a
  Lean placeholder.

- 2026-06-13 focused §1.15 displayed inverse-iteration near-parallel bridge:
  `lake build LeanFpAnalysis.FP.Analysis.BeneficialRounding` succeeded, and
  `lake env lean examples/LibraryLookup.lean >
  /private/tmp/librarylookup-ch1-beneficial-near-parallel.out` succeeded. The
  focused placeholder scan on
  `LeanFpAnalysis/FP/Analysis/BeneficialRounding.lean` and
  `examples/LibraryLookup.lean` returned no matches; trailing-whitespace and
  `git diff --check --` passed for the touched Lean/docs surfaces. The focused
  axiom audit for
  `beneficialPower_inverseIteration_near_parallel_error_eigenResidual_eq`,
  `beneficialPower_inverseIteration_near_parallel_error_eigenResidual_norm_le`,
  and
  `beneficialPower_inverseIteration_near_parallel_error_eigenResidual_norm_le_of_residual_norm_le`
  reports only `[propext, Classical.choice, Quot.sound]`. This closes the
  displayed-matrix specialization of the near-parallel residual bridge without
  enumerating finite input cases; the concrete rounded shifted-solve trace and
  cited perturbation theorem remain open.

- 2026-06-13 focused §1.7 finite round-to-even trig-output wrapper:
  `lake build LeanFpAnalysis.FP.Analysis.TrigCancellation` succeeded, and
  `lake env lean examples/LibraryLookup.lean >
  /private/tmp/librarylookup-ch1-trig-finite-round-final.out` succeeded. The
  lookup output has 55410 lines. The focused placeholder scan on
  `LeanFpAnalysis/FP/Analysis/TrigCancellation.lean` and
  `examples/LibraryLookup.lean` returned no matches; trailing-whitespace and
  `git diff --check --` passed for the touched Lean/docs surfaces. The focused
  axiom audit for `trigCancellationFiniteRoundToEvenCos_abs_error_le`,
  `trigCancellationFiniteRoundToEvenSinHalf_abs_error_le`,
  `trigCancellationDirectScaledFiniteRoundToEvenCos_abs_error_le`,
  `trigCancellationRewriteScaledFiniteRoundToEvenSinHalf_abs_error_le`, and
  `trigCancellationRewriteScaledFiniteRoundToEvenSinHalf_abs_error_le_direct_cos_bound`
  reports only `[propext, Classical.choice, Quot.sound]`. This closes the
  finite-normal finite round-to-even selector layer for the §1.7 supplied
  cosine and sine-half approximation budgets; full named libm/IEEE-library
  sine/cosine implementations remain outside this ideal output-selector
  contract if required.

- 2026-06-13 focused §1.8 finite-normal IEEE guard: added the reusable
  finite-normal no-flag/value-field theorem family in
  `FloatingPointArithmetic.lean` for primitive binary operations and square
  root, in nearest/even and arbitrary rounding modes. Reran
  `lake build LeanFpAnalysis.FP.Analysis.FloatingPointArithmetic` and
  `lake build LeanFpAnalysis.FP.Analysis.Quadratic`; both exited successfully.
  Reran `lake env lean examples/LibraryLookup.lean >
  /private/tmp/librarylookup-ch1-quadratic-finite-normal-guard-final.out`; it
  exited successfully and produced 55586 lookup lines. The focused axiom audit
  for the new finite-normal guard theorem family reports only
  `[propext, Classical.choice, Quot.sound]`.

- 2026-06-13 focused §1.8 displayed twice-precision trace: added
  `quadraticOverflowExample_singleOverflow_doubleRoundedDiscriminantTrace`,
  a source-facing wrapper that combines the single-precision `b*b` overflow
  fact with the actual IEEE-double rounded-intermediate discriminant trace's
  normal-range, no-flag, and value-field theorems. Reran
  `lake build LeanFpAnalysis.FP.Analysis.Quadratic`; it exited successfully.
  Reran `lake env lean examples/LibraryLookup.lean >
  /private/tmp/librarylookup-ch1-quadratic-twice-trace.out`; it exited
  successfully and produced 56062 lookup lines. The focused axiom audit for
  the new wrapper reports only `[propext, Classical.choice, Quot.sound]`.

- 2026-06-13 focused §1.9 supplied negative aggregate final trace: added
  `sampleVarianceOnePassIeeeSingleNegativeAggregateTrace_eq_neg_sixteen`,
  `sampleVarianceOnePassIeeeSingleNegativeAggregateTrace_lt_zero`, and
  `sampleVarianceOnePassIeeeSingleNegativeAggregateTrace_relError`, plus the
  finite-input and numerator certificates. This closes the binary32
  final-operation diagnostic from supplied aggregates `300059968` and
  `300060000`, while preserving the separate fact that the actual
  `[10000,10001,10002]` binary32 accumulation trace returns `0`. Reran
  `lake build LeanFpAnalysis.FP.Analysis.SampleVariance`; it exited
  successfully. Reran `lake env lean examples/LibraryLookup.lean >
  /private/tmp/librarylookup-ch1-samplevariance-negative-finaltrace.out`; it
  exited successfully and produced 56102 lookup lines. The focused axiom audit
  for the new theorem surface reports only
  `[propext, Classical.choice, Quot.sound]`.

- 2026-06-13 focused §1.12.3 reverse inverse-square high-prefix finite-cell
  adapters: added
  `inverseSquareExactReverseTenPowNineHighPrefix_mem_candidateWindowCellGuard`,
  `inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound_pos`,
  and
  `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget_of_eq_exact`.
  Reran `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`;
  it exited successfully. Reran `lake env lean examples/LibraryLookup.lean >
  /private/tmp/librarylookup-ch1-inverse-square-cellguard.out`; it exited
  successfully and produced 56236 lookup lines. The focused placeholder scan,
  trailing-whitespace scan, and `git diff --check --` all passed for the touched
  Lean/docs surfaces. The focused axiom audit for the three new adapter
  theorems reports only `[propext, Classical.choice, Quot.sound]`. This closes
  non-vacuity and exact-prefix bridge obligations for the strict finite-cell
  route; the actual rounded high-prefix membership theorem remains the open
  §1.12.3 frontier.

- 2026-06-13 focused §1.15 componentwise near-parallel solve-error certificate:
  added
  `beneficialPower_inverseIteration_near_parallel_error_eigenResidual_norm_le_of_componentwise_common_scalar`,
  `beneficialPowerFirstStep_perturbed_vecNorm2_le_of_row_sum_abs_le`, and
  `beneficialPowerFirstStep_perturbed_vecNorm2_le_of_entry_abs_le`.
  For the displayed zero-eigenvector start `[1,1,1]^T`, this proves that if
  every shifted-solve error component is within `eps` of a common scalar
  `eta`, then the inverse-iteration eigen-residual norm is bounded by
  `A_norm*(sqrt 3*eps)`. This reduces the open perturbation obligation to a
  concrete componentwise/common-direction certificate. For the first
  power-method step with a stored perturbation, row-sum radius `eps` now gives
  norm at most `sqrt 3*eps`, and entrywise radius `eps` gives norm at most
  `sqrt 3*(3*eps)`. These theorems do not reconstruct the hidden MATLAB/IEEE
  shifted-solve trace or the rounded stored matrix. Also restored the missing
  `SquareDifference` import in `examples/LibraryLookup.lean`, which unblocked
  the existing Chapter 3 difference-of-squares lookup checks during the full
  lookup gate. Reran `lake build LeanFpAnalysis.FP.Analysis.BeneficialRounding`,
  `lake build LeanFpAnalysis.FP.Algorithms.SquareDifference`, and
  `lake build LeanFpAnalysis.FP.Algorithms.MatMulBackwardError`; all exited
  successfully. Reran `lake env lean examples/LibraryLookup.lean >
  /private/tmp/librarylookup-ch1-beneficial-budget.out`; it exited
  successfully and produced 56422 lookup lines. The focused axiom audit for
  the three new theorems reports only `[propext, Classical.choice, Quot.sound]`. The
  focused placeholder scan on `BeneficialRounding.lean` and
  `examples/LibraryLookup.lean` returned no matches, and `git diff --check --`
  passed for the touched Lean/docs surfaces.

- 2026-06-13 focused §1.15 perturbed first-step exact row-sum certificate:
  added `beneficialPowerFirstStep_perturbed_eq_zero_iff_row_sums_zero`,
  `beneficialPowerFirstStep_perturbed_vecNorm2_eq_zero_iff_row_sums_zero`, and
  `beneficialPowerFirstStep_perturbed_vecNorm2_ge_of_row_sum_abs_ge`. These
  prove that the displayed first perturbed power-method vector and its
  Euclidean norm vanish exactly when every stored-perturbation row sum
  vanishes, and that any supplied row-sum magnitude lower bound is a lower
  bound for the first-step norm. Together with the existing upper-budget
  theorems, this turns the §1.15 first-step perturbation substrate into a
  two-sided, non-enumerative row-sum certificate. The concrete IEEE-double
  entrywise-storage vector and source-scale `10^-16` magnitude are closed in
  the later first-step entries; this row-sum certificate still does not derive
  a hidden MATLAB primitive-operation/BLAS matvec trace or the 38-iteration
  convergence observation. Reran
  `lake build LeanFpAnalysis.FP.Analysis.BeneficialRounding`; it exited
  successfully. Reran `lake build LeanFpAnalysis.FP.Algorithms.ContinuedFraction`
  to restore a missing lookup dependency `.olean`; it exited successfully.
  Reran `lake env lean examples/LibraryLookup.lean >
  /private/tmp/librarylookup-ch1-beneficial-exact-row-sums.out`; it exited
  successfully and produced 56501 lookup lines. The focused axiom audit for
  the three new theorems reports only
  `[propext, Classical.choice, Quot.sound]`. The focused placeholder scan and
  trailing-whitespace scan on the touched Lean/docs surfaces returned no
  matches, and `git diff --check --` passed for the tracked touched lookup
  surfaces.

- 2026-06-13 focused §1.15 left-to-right rounded-add operation-order caveat:
  added `beneficialPowerMatrixIeeeDoubleRoundedFirstStepLeftToRight`,
  `ieeeDoubleFormat_two_pow_neg54_finiteSystem`,
  `ieeeDoubleFormat_two_pow_neg55_finiteSystem`,
  `ieeeDoubleFormat_half_plus_two_pow_neg55_rounds_to_half`,
  `ieeeDoubleFormat_neg_half_plus_two_pow_neg55_rounds_to_neg_half`,
  `beneficialPowerMatrixIeeeDoubleRoundedFirstStepLeftToRight_two_component_eq_zero`,
  and `beneficialPowerMatrixIeeeDoubleRoundedFirstStepLeftToRight_ne_firstStep`.
  These show that a concrete left-to-right rounded-add row-sum trace is not the
  same as the exact entrywise-stored row-sum vector: the third row first rounds
  `fl(fl(-1/10)+fl(-2/5))` to `-1/2`, and adding the stored `1/2` gives final
  third component `0`, whereas the exact entrywise-stored row sum is `-2^-55`.
  This narrows the hidden MATLAB first-step gap to an operation-order/BLAS trace
  question and prevents closing that gap by the exact row-sum theorem alone.
  Reran `lake build LeanFpAnalysis.FP.Analysis.BeneficialRounding`; it exited
  successfully.

- 2026-06-13 focused §1.15 two-component power-method convergence-rate
  substrate: added `powerMethodIterate`,
  `powerMethodIterate_two_eigencomponents`,
  `powerMethod_component_abs_ratio_eq_initial_mul_spectral_ratio`,
  `powerMethod_component_abs_ratio_le_geometric_of_spectral_ratio_le`, and
  `powerMethod_component_abs_ratio_tendsto_zero_of_spectral_ratio_lt_one`.
  These prove the source's linear-rate mechanism in the compact two-component
  model: after `k` unnormalized power-method steps, dominant and other
  eigenvector components are scaled by their eigenvalue powers, and the
  non-dominant/dominant scalar ratio is the initial ratio times the spectral
  ratio to the `k`th power, hence tends to zero when the spectral ratio is
  strictly below one. This is a theory-layer closure, not a concrete proof of
  the rounded `A+DeltaA` dominant eigenpair, hidden MATLAB/BLAS trace, or
  38-iteration observation. Reran
  `lake build LeanFpAnalysis.FP.Analysis.BeneficialRounding`; it exited
  successfully. Rebuilt `LeanFpAnalysis.FP.Algorithms.KahanAbsolute` to refresh
  a stale lookup dependency, then reran
  `lake env lean examples/LibraryLookup.lean >
  /private/tmp/chapter01_lookup_check.out`; it exited successfully and produced
  57061 lookup lines. The focused axiom audit for the four new public theorem
  surfaces reports only `[propext, Classical.choice, Quot.sound]`. The focused
  placeholder scan and trailing-whitespace scan on the touched Lean/docs
  surfaces returned no matches, and
  `git diff --check -- LeanFpAnalysis/FP/Analysis/BeneficialRounding.lean
  examples/LibraryLookup.lean docs/LIBRARY_LOOKUP.md
  docs/CHAPTER01_FULL_FORMALIZATION_LEDGER.md` passed.

- 2026-06-13 focused §1.15 right-to-left rounded-add operation-order
  certificate: added `beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft`
  and the component/equality theorems
  `beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft_zero_component_eq`,
  `beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft_one_component_eq`,
  `beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft_two_component_eq`,
  and `beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft_eq_firstStep`.
  This proves that the right-to-left rounded-add row-sum trace, after entrywise
  IEEE-double storage and with multiplication by the exact start-vector entries
  `1` suppressed, gives exactly `[2^-54, -2^-54, -2^-55]^T` and is
  extensionally equal to the entrywise-storage first-step vector. Together with
  the left-to-right caveat, this narrows the remaining MATLAB first-step gap to
  identifying or assuming the actual BLAS/matvec operation order, rather than
  proving thousands of cases. Reran
  `lake build LeanFpAnalysis.FP.Analysis.BeneficialRounding`; it exited
  successfully. Rebuilt stale lookup imports
  `LeanFpAnalysis.FP.Algorithms.DotProduct` and
  `LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`, then reran
  `lake env lean examples/LibraryLookup.lean >
  /private/tmp/chapter01_lookup_check.out`; it exited successfully and produced
  57178 lookup lines. The focused axiom audit for the four new right-to-left
  public theorem surfaces reports only
  `[propext, Classical.choice, Quot.sound]`. The focused placeholder scan,
  trailing-whitespace scan, and `git diff --check --` on the touched
  Lean/docs surfaces passed.

- 2026-06-13 focused §1.15 finite-tail power-method convergence bridge:
  added `matMulVec_fin_sum_right`,
  `vecNorm2_finset_sum_le`, `vecNorm2_fin_sum_le`,
  `powerMethodIterate_dominant_plus_finite_tail`,
  `powerMethod_finite_tail_abs_sum_ratio_le_geometric_of_spectral_ratio_le`,
  `powerMethod_finite_tail_geometric_bound_tendsto_zero`, and
  `powerMethod_finite_tail_abs_sum_ratio_tendsto_zero_of_geometric_bound`,
  plus the norm-level theorems
  `powerMethod_finite_tail_vecNorm2_ratio_le_geometric_of_spectral_ratio_le`
  and
  `powerMethod_finite_tail_vecNorm2_ratio_tendsto_zero_of_geometric_bound`,
  and the direct iterate-residual theorems
  `powerMethodIterate_dominant_scaled_residual_ratio_le_geometric_of_finite_tail`
  and `powerMethodIterate_dominant_scaled_residual_tendsto_zero_of_finite_tail`.
  These prove the finite-family version of the source's power-method theory
  sentence: a dominant eigencomponent plus any finite tail of right-eigenvector
  components evolves by scaling every component by its eigenvalue power; a
  uniform tail spectral-ratio bound `q` gives aggregate coefficient and
  Euclidean-norm `q^k` tail bounds; and those normalized aggregate tails tend
  to zero when `0 <= q < 1`. This is the intended non-enumerative closure, not
  a component-by-component proof.
  Remaining §1.15 power-method work is now the concrete decomposition and
  dominant-eigenpair perturbation data for stored `A+DeltaA`, the hidden
  MATLAB/BLAS matvec/printout trace, and the 38-iteration observation. Reran
  `lake build LeanFpAnalysis.FP.Analysis.BeneficialRounding`; it exited
  successfully. Rebuilt stale lookup imports
  `LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`,
  `LeanFpAnalysis.FP.Analysis.NonrandomRounding`, and
  `LeanFpAnalysis.FP.Algorithms`, then reran
  `lake env lean examples/LibraryLookup.lean >
  /private/tmp/chapter01_lookup_check.out`; it exited successfully and produced
  57413 lookup lines. The focused axiom audits for the finite-tail,
  norm-level, and direct residual public theorem surfaces report only
  `[propext, Classical.choice, Quot.sound]`.

- 2026-06-13 §1.15 beneficial power-method bottleneck freeze: created
  `docs/CHAPTER01_BENEFICIAL_POWER_METHOD_BOTTLENECK.md` for the remaining
  concrete MATLAB/stored-matrix power-method gap. The bottleneck records that
  the finite-tail convergence theorem is closed, so the next real dependency is
  a concrete dominant-eigenpair/eigencomponent certificate for the stored
  `A+DeltaA`, plus a source or assumption for the MATLAB/BLAS operation order
  and, if required, a normalization/display certificate for the 38-iteration
  observation. It explicitly rejects both thousands-of-cases enumeration and
  silently identifying the entrywise row-sum theorem with MATLAB's hidden
  operation order.

- 2026-06-13 §1.15 beneficial power-method proof-source acquisition: created
  `docs/CHAPTER01_PROOF_SOURCE_LEDGER.md` with active chain `C1.15-BPM`.
  The ledger maps the source claim in `references/Chapter01_full.pdf` §1.15
  to the missing stored-matrix dominant-eigencomponent certificate, MATLAB/BLAS
  operation-order certificate, and optional 38-iteration display certificate.
  It records Greenbaum--Li--Overton, "First-order Perturbation Theory for
  Eigenvalues and Eigenvectors", arXiv:1903.00785, as an advisory source for
  the simple eigenvalue/eigenvector perturbation route, Bauer--Fike as an
  eigenvalue-gap candidate that is insufficient by itself, and the alternate
  concrete `3 x 3` stored-matrix spectral-certificate route. No paper-level
  claim is closed by citation. The subsequent Lean handoff theorem
  `beneficialPowerStoredStart_dominant_component_certificate_scaled_residual_tendsto_zero`
  now proves that any concrete stored-matrix dominant-component certificate
  feeds the already closed finite-tail power-method theorem; the next Lean
  target is constructing that certificate, not enumerating iterations.

- 2026-06-13 focused §1.15 concrete IEEE-double full first-step vector:
  added `ieeeDoubleFormat_one_tenth_finiteNormalRange`,
  `ieeeDoubleFormat_three_tenths_finiteNormalRange`,
  `ieeeDoubleFormat_seven_tenths_finiteNormalRange`,
  `ieeeDoubleFormat_one_tenth_rounds_to`,
  `ieeeDoubleFormat_three_tenths_rounds_to`,
  `ieeeDoubleFormat_seven_tenths_rounds_to`,
  `ieeeDoubleFormat_neg_one_tenth_rounds_to`,
  `ieeeDoubleFormat_neg_two_fifths_rounds_to`,
  `ieeeDoubleFormat_neg_three_tenths_rounds_to`,
  `ieeeDoubleFormat_one_half_finiteSystem`,
  `ieeeDoubleFormat_one_half_rounds_to`,
  `beneficialPowerMatrixIeeeDoubleRoundedFirstStep`,
  `beneficialPowerMatrixIeeeDoubleRounded_row_one_sum_eq`,
  `beneficialPowerMatrixIeeeDoubleRounded_row_two_sum_eq`,
  `beneficialPowerMatrixIeeeDoubleRounded_firstStep_one_component_eq`,
  `beneficialPowerMatrixIeeeDoubleRounded_firstStep_two_component_eq`, and
  `beneficialPowerMatrixIeeeDoubleRounded_firstStep_eq`, and
  `beneficialPowerMatrixIeeeDoubleRounded_firstStep_abs_between_one_e17_one_e16`.
  Together with the previous first-row theorem, this proves the full
  unnormalized first power-method step after entrywise IEEE-double storage is
  exactly `[2^-54, -2^-54, -2^-55]^T`, and proves every component has magnitude
  between `10^-17` and `10^-16`. This closes the rounded matrix/vector
  first-step vector and source-scale `10^-16` magnitude at the repository's
  finite round-to-even storage layer, without enumerating subsequent MATLAB
  iterations. The remaining §1.15 open items are a hidden MATLAB
  primitive-operation/BLAS matvec and printout trace if that exact
  implementation path is required, the 38-iteration observation,
  dominant-eigenpair perturbation theory for the rounded matrix, and the
  inverse-iteration
  near-parallel solve-error source theorem. Also repaired a local namespace
  call in `FloatingPointArithmetic.lean` by replacing method syntax for
  `finiteRoundToEvenOp_add_oppositeSign_sameExponent_eq_exact` with the local
  theorem name, restoring that dependency build. Reran
  `lake build LeanFpAnalysis.FP.Analysis.FloatingPointArithmetic`,
  `lake build LeanFpAnalysis.FP.Analysis.BeneficialRounding`,
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`,
  `lake build LeanFpAnalysis.FP.Algorithms.SumTree`,
  `lake build LeanFpAnalysis.FP.Algorithms.InsertionSum`,
  `lake build LeanFpAnalysis.FP.Analysis.Problem2_10`, and
  `lake build LeanFpAnalysis.FP.Algorithms.RandNLA.ElementwiseSpectral`; all
  exited successfully, restoring lookup dependencies as needed. Reran
  `lake env lean examples/LibraryLookup.lean >
  /private/tmp/librarylookup-ch1-beneficial-ieee-fullfirststep.out`; it exited
  successfully and produced 56831 lookup lines. The focused axiom audit for
  the ten new public theorem surfaces reports only
  `[propext, Classical.choice, Quot.sound]`. The focused placeholder scan and
  trailing-whitespace scan on the touched Lean/docs surfaces returned no
  matches, and `git diff --check --` passed for the tracked touched lookup and
  dependency surfaces.

- 2026-06-13 focused §1.15 concrete IEEE-double first-row storage certificate:
  added `ieeeDoubleFormat_one_fifth_finiteNormalRange`,
  `ieeeDoubleFormat_two_fifths_finiteNormalRange`,
  `ieeeDoubleFormat_three_fifths_finiteNormalRange`,
  `ieeeDoubleFormat_one_fifth_rounds_to`,
  `ieeeDoubleFormat_two_fifths_rounds_to`,
  `ieeeDoubleFormat_three_fifths_rounds_to`,
  `ieeeDoubleFormat_neg_three_fifths_rounds_to`,
  `beneficialPowerMatrixIeeeDoubleRounded`,
  `beneficialPowerMatrixIeeeDoubleRounded_row_zero_sum_eq`,
  `beneficialPowerMatrixIeeeDoubleRounded_firstStep_zero_component_eq`,
  `beneficialPowerMatrixIeeeDoubleRounded_firstStep_vecNorm2_pos`, and
  `beneficialPowerMatrixIeeeDoubleRounded_firstStep_vecNorm2_ge_two_pow_neg54`.
  These close the first concrete rounded-storage slice for the §1.15
  power-method example: the IEEE-double rounded first row has sum exactly
  `2^-54`, the first rounded power-method component is exactly `2^-54`, and
  the first-step Euclidean norm is at least `2^-54`. This attacks the actual
  rounded-entry/perturbation-size gap directly, without enumerating a MATLAB
  trace. The later full-vector entry closes the rest of the entrywise-storage
  first-step vector and its source-scale `10^-16` magnitude; the remaining open
  part is a hidden MATLAB primitive-operation/BLAS matvec trace if required,
  the 38-iteration observation, and dominant-eigenpair perturbation theory for
  the rounded matrix. Reran `lake build LeanFpAnalysis.FP.Analysis.BeneficialRounding`;
  it exited successfully. Reran
  `lake build LeanFpAnalysis.FP.Analysis.FloatingPointArithmetic` to restore a
  missing dependency `.olean` needed by the focused axiom scratch; it exited
  successfully. Reran `lake env lean examples/LibraryLookup.lean >
  /private/tmp/librarylookup-ch1-beneficial-ieee-firstrow.out`; it exited
  successfully and produced 56627 lookup lines. The focused axiom audit for
  the eight new public theorem surfaces reports only
  `[propext, Classical.choice, Quot.sound]`. The focused placeholder scan and
  trailing-whitespace scan on the touched Lean/docs surfaces returned no
  matches, and `git diff --check --` passed for the tracked touched lookup
  surfaces.

- 2026-06-14 focused §1.12.3 reverse inverse-square high-prefix `8192` split:
  added `inverseSquareTerm_le_two_pow_neg_26_of_ge_8192`,
  `inverseSquareReverseTenPowNineHighPrefix_index_ge_8192`,
  `inverseSquareTerm_le_two_pow_neg_26_of_reverse_ten_pow_nine_high_binade`,
  `inverseSquareSingleReverseTenPowNineHighPrefixState_split_8192`, and
  `inverseSquareExactReverseTenPowNineHighPrefix_split_8192`,
  `inverseSquareExactReverseTenPowNineHighPrefixBefore8192_le_inv_8192`, and
  `inverseSquareSingleReverseTenPowNineHighPrefixBefore8192_le_inv_4096`,
  `inverseSquareExactReverseBinade8192To4097_le_inv_8192`, and
  `inverseSquareSingleReverseBinade8192To4097_le_start_add_inv_4096`, plus the
  route guard
  `inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound_lt_inv_4096`.
  These close the first binade-scale high-prefix dependency for the D1 route:
  the earlier `10^9, ..., 8193` block has the sharper `2^-26` term bound, both
  the rounded and exact high-prefix states split into that earlier block
  followed by `8192, ..., 4097`, and the pre-binade exact/rounded states are
  bounded by `1/8192` and `1/4096`, respectively. The final-binade exact mass
  is at most `1/8192`, and the whole rounded final-binade increment from any
  finite binary32 start is at most `1/4096`. The guard proves the coarse
  `1/4096` budget is still larger than the strict finite-cell D1 margin. This
  is not a suffix replay and does not close
  `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow`. Reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`; it
  exited successfully. Rebuilt the missing cache object with
  `lake build LeanFpAnalysis.FP`; it exited successfully with pre-existing
  linter warnings in QR/FastMatMul files outside this Chapter 1 change. Also
  rebuilt the stale lookup dependencies
  `LeanFpAnalysis.FP.Analysis.Problem2_10` and
  `LeanFpAnalysis.FP.Algorithms.KahanAbsolute`; both exited successfully. Reran
  `lake env lean examples/LibraryLookup.lean >
  /private/tmp/librarylookup-ch1-reverse-8192-split.out`; it exited
  successfully and produced 59867 lookup lines, including all ten new names.
  The focused axiom audit for the ten theorem declarations reports only
  `[propext, Classical.choice, Quot.sound]`. The focused placeholder scan on
  the touched Lean/lookup files returned no matches, and
  `git diff --check --` passed for the touched Lean/docs/lookup surfaces.

- 2026-06-14 focused §1.12.3 reverse inverse-square exact earlier-block start
  window: added `inverseSquareSingleReverseHighPrefixBefore8192WindowLower`,
  `inverseSquareSingleReverseHighPrefixBefore8192WindowUpper`, and
  `inverseSquareExactReverseTenPowNineHighPrefixBefore8192_mem_startWindow`.
  Also added `inverseSquareSingleReverseHighBinade8190To4097Prefix_eq`,
  `inverseSquareSingleReverseHighBinade8190To4097WindowEndpointCertificateBool`,
  `inverseSquareSingleReverseHighBinade8190To4097WindowEndpointCertificateBool_eq_true`,
  and
  `inverseSquareSingleReverseHighBinade8190To4097WindowEndpointCertificate`.
  This closes the exact side of the `8192` split start-window dependency and
  the same-exponent tail certificate for the final high-prefix binade: Lean now
  proves by telescoping that the exact `10^9, ..., 8193` mass lies in the
  binary32 window intended to feed the compact final high-prefix binade route,
  proves the `8190^{-2}, ..., 4097^{-2}` scaled mantissa prefix total is
  `8385036`, and kernel-checks the 4094-step endpoint-safety predicate at
  scale `q = 37`. This still does not close
  `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow`; the next
  D1 dependencies are the rounded earlier-block membership in the same start
  window and the final-binade window map packaging the two boundary additions
  `8192^{-2}`, `8191^{-2}` plus the certified same-exponent tail. Reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`; it
  exited successfully. Rebuilt the aggregate dependency with
  `lake build LeanFpAnalysis.FP.Analysis`; it exited successfully and restored
  the canonical
  `.lake/build/lib/lean/LeanFpAnalysis/FP/Analysis/InstabilityWithoutCancellation.olean`
  object needed by lookup. The focused axiom scratch
  `/private/tmp/ch1_reverse_before8192_startwindow_axioms.lean` checked the two
  new endpoint definitions and printed axioms for the four new theorem
  declarations; it reported only `[propext, Classical.choice, Quot.sound]`.
  Reran `lake build LeanFpAnalysis.FP.Analysis.Problem2_10`; it exited
  successfully, restoring a stale lookup dependency. Reran
  `lake env lean examples/LibraryLookup.lean >
  /private/tmp/librarylookup-ch1-before8192-startwindow.out`; it exited
  successfully and produced 60055 lookup lines. The focused placeholder scan
  on the touched Lean/lookup files returned no matches, and
  `git diff --check --` passed for the touched Lean/docs/lookup surfaces.

- 2026-06-14 focused §1.12.3 reverse inverse-square final high-binade window
  map: added the post-`8192` and post-`8191` boundary windows, proved the
  rounded `8192^{-2}` boundary map by finite-endpoint nearest rounding, proved
  the rounded `8191^{-2}` boundary map by adjacent-cell nearest rounding, and
  consumed the already checked `8190^{-2}, ..., 4097^{-2}` tail certificate by
  `inverseSquareSingleReverseHighBinadeTailWindow_prefix_mem`. The composed
  theorem
  `inverseSquareSingleReverseHighBinade8192To4097WindowMapsToCandidate_closed`
  now maps every pre-binade start-window value through `8192^{-2}, ..., 4097^{-2}`
  into `inverseSquareSingleReverseHighPrefixCandidateWindowLower`/`Upper`.
  Added
  `inverseSquareSingleReverseTenPowNineHighPrefixBefore8192InStartWindow` and
  `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_before8192StartWindow`
  to make the remaining rounded earlier-block obligation explicit. This closes
  the final-binade map dependency but still does not close the full D1 printed
  reverse-order theorem, because the rounded `10^9, ..., 8193` pre-binade state
  has not yet been proved to enter the start window. Reran
  `lake build LeanFpAnalysis.FP.Analysis.InstabilityWithoutCancellation`; it
  exited successfully.

- 2026-06-14 focused §1.12.3 reverse inverse-square rounded earlier-block
  audit: rechecked the live D1 dependency after the final high-binade map was
  closed.  The remaining paper-level gap is still exactly
  `inverseSquareSingleReverseTenPowNineHighPrefixBefore8192InStartWindow`,
  the assertion that the rounded `10^9, ..., 8193` pre-binade state lies
  between `inverseSquareSingleReverseHighPrefixBefore8192WindowLower` and
  `inverseSquareSingleReverseHighPrefixBefore8192WindowUpper`.  The existing
  standard-model accumulated-error envelope and the `1/4096` rounded
  earlier-block coarse bound remain too weak for the few-thousand-ulp window,
  so no full D1 printed reverse-order theorem is marked closed.  A follow-up
  Lean step names the observed rounded earlier-block candidate
  `inverseSquareSingleReverseTenPowNineHighPrefixBefore8192Candidate`
  (`0x38fff94f`), proves
  `inverseSquareSingleReverseTenPowNineHighPrefixBefore8192Candidate_mem_startWindow`,
  defines
  `inverseSquareSingleReverseTenPowNineHighPrefixBefore8192EqCandidate`, and
  proves
  `inverseSquareSingleReverseTenPowNineHighPrefixBefore8192InStartWindow_of_eq_candidate`.
  Thus the concrete equality route is now the smaller live target; the actual
  equality is not yet proved.  The next non-enumerative route is a dyadic
  finite-endpoint interval invariant for the rounded earlier block; a
  billion-step Boolean certificate or thousands of copied local step theorems
  is explicitly rejected as the proof shape.

- 2026-06-14 focused §1.12.3 reverse inverse-square no-change dependency:
  closed
  `inverseSquareSingleForwardStep_normalizedValue_eq_self_of_scaled_half_ulp_at_scale`,
  the arbitrary-exponent IEEE-single rule saying that if `2^q < k^2`, then
  adding `1/k^2` to a positive normalized state in the exponent band encoded
  by `q` rounds back to the same state.  This is the no-change companion to
  `inverseSquareSingleForwardStep_normalizedValue_nearest_mantissa_of_scaled_bounds_at_scale`
  and supplies a local rule needed for a compressed dyadic finite-endpoint
  invariant over the large rounded earlier block.  The actual equality
  `inverseSquareSingleReverseTenPowNineHighPrefixBefore8192EqCandidate` is
  still open.
