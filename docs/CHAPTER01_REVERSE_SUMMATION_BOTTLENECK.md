# Chapter 1 Reverse Summation Bottleneck

Source: `references/Chapter01_full.pdf`, Section 1.12.3, reverse-order
single-precision summation of
`sum_{i=1}^{10^9} 1 / i^2`, with printed value `1.64493406`.

Final target:

```lean
inverseSquareSingleReverseAccumulator (10 ^ 9) =
  inverseSquareSingleReversePrintedAccumulator
```

## Closed Route So Far

- The `10^9` reverse accumulator is split at the final `4096` low-index terms by
  `inverseSquareSingleReverseAccumulator_ten_pow_nine_split_4096`.
- The concrete high-prefix candidate is
  `inverseSquareSingleReverseTenPowNineHighPrefixCandidate`.
- The concrete low-index suffix from that candidate is closed by
  `inverseSquareSingleReverseCandidateSuffixMapsToPrinted_closed`.
- The current candidate-window transfer theorem is
  `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_candidateWindow_certificates`.
- The first interval transition inside the candidate-window suffix map is now
  closed by
  `inverseSquareSingleReverseCandidateWindow_add_4096_term_mem_after4096Window`.
  It maps the full 1024-ulp high-prefix candidate window through exact addition
  of `4096^{-2}` into a 512-ulp post-`4096` window.
- The rounded version of the same first transition is closed by
  `inverseSquareSingleReverseCandidateWindow_round_4096_step_mem_after4096Window`,
  using
  `FloatingPointFormat.nearestRoundingToFinite_mem_Icc_of_finite_endpoints`.
- The original candidate-window suffix map is reduced past the first rounded
  step by
  `inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_after4096Window`.
- The post-`4096` whole-window suffix map is reduced past the rounded
  `4095^{-2}` step by
  `inverseSquareSingleReverseAfter4096WindowMapsToPrinted_of_after4095Window`.
- The post-`4095` suffix map is now reduced to a same-exponent band-window
  certificate plus a before-`2048` suffix certificate by
  `inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_band4094_to_before2048Window`.
- The two endpoints of the post-`4095` window are now proved to propagate
  through the whole `4094^{-2}, ..., 2049^{-2}` band to the corresponding
  before-`2048` window endpoints by
  `inverseSquareSingleReverseAfter4095WindowLower_band4094_to_before2048_eq`
  and
  `inverseSquareSingleReverseAfter4095WindowUpper_band4094_to_before2048_eq`.
- The generic adjacent-midpoint finite-rounding exclusions needed for the
  interior lift are now proved by
  `FloatingPointFormat.nearestRoundingToFinite_ge_of_adjacent_midpoint` and
  `FloatingPointFormat.nearestRoundingToFinite_le_of_adjacent_midpoint`, with
  finite-system adjacency side lemmas for values outside the adjacent cell.
- The full arbitrary-start same-exponent band-window map is now closed by
  `inverseSquareSingleReverseAfter4095BandWindow_round_step_mem`,
  `inverseSquareSingleReverseAfter4095BandWindow_prefix_mem`, and
  `inverseSquareSingleReverseAfter4095Band4094ToBefore2048Window_closed`.
  Consequently the post-`4095` suffix map is reduced directly to the
  before-`2048` window suffix map by
  `inverseSquareSingleReverseAfter4095WindowMapsToPrinted_of_before2048Window`.
- The before-`2048` whole-window suffix map is now reduced past the rounded
  `2048^{-2}` boundary step and the `2047^{-2}, ..., 1025^{-2}` band by
  `inverseSquareSingleReverseBefore2048Window_round_2048_step_mem_after2048Window`,
  `inverseSquareSingleReverseAfter2048BandWindow_round_step_mem`,
  `inverseSquareSingleReverseAfter2048BandWindow_prefix_mem`, and
  `inverseSquareSingleReverseAfter2048Band2047ToBefore1024Window_closed`.
  Consequently the candidate-window suffix route is reduced directly to the
  before-`1024` window suffix map by
  `inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before1024Window`.
- The before-`1024` whole-window suffix map is now reduced past the rounded
  `1024^{-2}` boundary step and the `1023^{-2}, ..., 513^{-2}` band by
  `inverseSquareSingleReverseBefore1024Window_round_1024_step_mem_after1024Window`,
  `inverseSquareSingleReverseAfter1024BandWindow_round_step_mem`,
  `inverseSquareSingleReverseAfter1024BandWindow_prefix_mem`, and
  `inverseSquareSingleReverseAfter1024Band1023ToBefore512Window_closed`.
  Consequently the candidate-window suffix route is reduced directly to the
  before-`512` window suffix map by
  `inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before512Window`.
- The before-`512` whole-window suffix map is now reduced past the rounded
  `512^{-2}` boundary step and the `511^{-2}, ..., 257^{-2}` band by
  `inverseSquareSingleReverseBefore512Window_round_512_step_mem_after512Window`,
  `inverseSquareSingleReverseAfter512BandWindow_round_step_mem`,
  `inverseSquareSingleReverseAfter512BandWindow_prefix_mem`, and
  `inverseSquareSingleReverseAfter512Band511ToBefore256Window_closed`.
  Consequently the candidate-window suffix route is reduced directly to the
  before-`256` window suffix map by
  `inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before256Window`.
- The before-`256` whole-window suffix map is now reduced past the rounded
  `256^{-2}` boundary step and the `255^{-2}, ..., 129^{-2}` band by
  `inverseSquareSingleReverseBefore256Window_round_256_step_mem_after256Window`,
  `inverseSquareSingleReverseAfter256BandWindow_round_step_mem`,
  `inverseSquareSingleReverseAfter256BandWindow_prefix_mem`, and
  `inverseSquareSingleReverseAfter256Band255ToBefore128Window_closed`.
  Consequently the candidate-window suffix route is reduced directly to the
  before-`128` window suffix map by
  `inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before128Window`.
- The before-`128` whole-window suffix map is now reduced past the rounded
  `128^{-2}` boundary step and the `127^{-2}, ..., 65^{-2}` band by
  `inverseSquareSingleReverseBefore128Window_round_128_step_mem_after128Window`,
  `inverseSquareSingleReverseAfter128BandWindow_round_step_mem`,
  `inverseSquareSingleReverseAfter128BandWindow_prefix_mem`, and
  `inverseSquareSingleReverseAfter128Band127ToBefore64Window_closed`.
  Consequently the candidate-window suffix route is reduced directly to the
  before-`64` window suffix map by
  `inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before64Window`.
- The before-`64` whole-window suffix map is now reduced past the rounded
  `64^{-2}` boundary step and the `63^{-2}, ..., 33^{-2}` band by
  `inverseSquareSingleReverseBefore64Window_round_64_step_mem_after64Window`,
  `inverseSquareSingleReverseAfter64BandWindow_round_step_mem`,
  `inverseSquareSingleReverseAfter64BandWindow_prefix_mem`, and
  `inverseSquareSingleReverseAfter64Band63ToBefore32Window_closed`.
  Consequently the candidate-window suffix route is reduced directly to the
  before-`32` window suffix map by
  `inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before32Window`.
- The before-`32` whole-window suffix map is now reduced past the rounded
  `32^{-2}` boundary step and the `31^{-2}, ..., 17^{-2}` band by
  `inverseSquareSingleReverseBefore32Window_round_32_step_mem_after32Window`,
  `inverseSquareSingleReverseAfter32BandWindow_round_step_mem`,
  `inverseSquareSingleReverseAfter32BandWindow_prefix_mem`, and
  `inverseSquareSingleReverseAfter32Band31ToBefore16Window_closed`.
  Consequently the candidate-window suffix route is reduced directly to the
  before-`16` window suffix map by
  `inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before16Window`.
- The before-`16` whole-window suffix map is now reduced past the rounded
  `16^{-2}` boundary step and the `15^{-2}, ..., 9^{-2}` band by
  `inverseSquareSingleReverseBefore16Window_round_16_step_mem_after16Window`,
  `inverseSquareSingleReverseAfter16BandWindow_round_step_mem`,
  `inverseSquareSingleReverseAfter16BandWindow_prefix_mem`, and
  `inverseSquareSingleReverseAfter16Band15ToBefore8Window_closed`.
  Consequently the candidate-window suffix route is reduced directly to the
  before-`8` window suffix map by
  `inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before8Window`.
- The before-`8` whole-window suffix map is now reduced past the rounded
  `8^{-2}` boundary step and the `7^{-2}, 6^{-2}, 5^{-2}` band by
  `inverseSquareSingleReverseBefore8Window_round_8_step_mem_after8Window`,
  `inverseSquareSingleReverseAfter8BandWindow_round_step_mem`,
  `inverseSquareSingleReverseAfter8BandWindow_prefix_mem`, and
  `inverseSquareSingleReverseAfter8Band7ToBefore4Window_closed`.
  Consequently the candidate-window suffix route is reduced directly to the
  before-`4` window suffix map by
  `inverseSquareSingleReverseCandidateWindowMapsToPrinted_of_before4Window`.
- The before-`4` whole-window suffix map is now closed by
  `inverseSquareSingleReverseBefore4WindowMapsToPrinted_closed`.  It uses
  final endpoint windows for the `4^{-2}` and `3^{-2}` steps plus a
  tie-to-even adjacent-bracket collapse for the `2^{-2}` step, then composes
  the exact `1^{-2}` final step.  The narrowed candidate-window suffix route is
  closed by `inverseSquareSingleReverseCandidateWindowMapsToPrinted_closed`.
- The closed suffix route now composes with a single high-prefix margin
  certificate by
  `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_abs_error_le_candidateWindowMarginShiftedLowerBound_closed`.
  The remaining D1 target is therefore the compact absolute-error bound
  from `inverseSquareSingleReverseTenPowNineHighPrefixState` to the exact
  high-prefix mass, not any low-index suffix case split.
- The same closed suffix route also composes with the new finite-cell guard
  route
  `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_candidateWindowCellGuard_closed`.
  Since the actual high-prefix state is already proved finite-system, it is
  enough to prove two strict inequalities against the predecessor of the lower
  candidate-window endpoint and the successor of the upper endpoint.
- The exact-prefix finite-cell adapters
  `inverseSquareExactReverseTenPowNineHighPrefix_mem_candidateWindowCellGuard`,
  `inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound_pos`,
  and
  `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget_of_eq_exact`
  close non-vacuity checks for the strict guard route: the exact high-prefix
  mass is strictly inside the predecessor/successor cell guard, the strict
  cell-margin radius is positive, and exact-prefix equality would discharge the
  strict margin target.

## Dependency Status

- D1: open. Prove rounded high-prefix candidate-window membership:
  `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow`.
- D1 reduced target: it is sufficient to prove
  `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowMarginTarget`,
  namely
  `|inverseSquareSingleReverseTenPowNineHighPrefixState -
    inverseSquareExactReverseAccumulatorFrom 0 (10 ^ 9) (10 ^ 9 - 4096)| ≤
    inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound`.
- D1 route guard closed:
  `inverseSquareSingleReverseTenPowNineHighPrefix_singleGammaGuard_not_valid`
  proves the standard recursive-summation `gamma (n-1)` guard is false for the
  `10^9 - 4096` high-prefix length at IEEE single unit roundoff, so the next
  proof route must be a local high-prefix interval/window or nearest-cell
  certificate.  The model-facing theorem
  `inverseSquareSingleReverseTenPowNineHighPrefix_singleGammaValid_not_valid`
  states the same obstruction directly for `gammaValid fp` whenever
  `fp.u = 2^-24`.
- D1 coarse accumulated-envelope guard closed:
  `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowMarginShiftedLowerBound_lt_coarseAccumulatedStdError`
  proves that the explicit candidate-window margin is smaller than the uniform
  coarse per-step error bound accumulated across the whole high-prefix length.
  The negated guard
  `inverseSquareSingleReverseTenPowNineHighPrefix_coarseAccumulatedStdErrorGuard_not_sufficient`
  records that this coarse envelope cannot directly prove the D1 margin target.
- D1 finite-format foothold closed:
  `inverseSquareSingleReverseAccumulatorFrom_finiteSystem_of_start` proves every
  concrete reverse accumulator state remains IEEE-single finite when started
  from a finite state, and
  `inverseSquareSingleReverseTenPowNineHighPrefixState_finiteSystem` specializes
  this to the actual `10^9, ..., 4097` rounded high-prefix state.
- D1 monotonicity foothold closed:
  `FloatingPointFormat.finiteRoundToEvenOp_add_ge_left_of_finiteSystem_of_nonneg`
  proves that finite round-to-even addition by a nonnegative quantity cannot
  return a value below the finite left input.  This lifts to
  `inverseSquareSingleForwardStep_ge_self_of_finiteSystem`,
  `inverseSquareSingleReverseAccumulatorFrom_start_le_of_finiteSystem`,
  `inverseSquareSingleReverseAccumulatorFrom_nonneg_of_start_nonneg`, and the
  actual high-prefix invariant
  `inverseSquareSingleReverseTenPowNineHighPrefixState_nonneg`.
- D1 error-envelope foothold closed:
  `FloatingPointFormat.finiteRoundToEvenOp_add_abs_error_le_right_of_finiteSystem_of_nonneg`
  proves that a rounded nonnegative addition has absolute error bounded by the
  added quantity when the left input is finite, and
  `FloatingPointFormat.finiteRoundToEvenOp_add_le_left_add_two_mul_right_of_finiteSystem_of_nonneg`
  converts this into a one-step upper increment bound.  The inverse-square
  wrappers
  `inverseSquareSingleForwardStep_abs_error_le_term_of_finiteSystem`,
  `inverseSquareSingleForwardStep_le_self_add_two_mul_term_of_finiteSystem`, and
  `inverseSquareSingleReverseAccumulatorFrom_le_start_add_two_mul_exact_zero_start`
  give a first block-level rounded-prefix envelope, specialized by
  `inverseSquareSingleReverseTenPowNineHighPrefixState_le_two_mul_exact` and
  `inverseSquareSingleReverseTenPowNineHighPrefixState_le_inv_2048`.
- D1 high-prefix standard-model foothold closed:
  `inverseSquareTerm_ten_pow_nine_ge_ieeeSingle_minNormal` and
  `inverseSquareTerm_ge_ieeeSingle_minNormal_of_pos_le_ten_pow_nine` prove that
  the high-prefix terms remain above binary32's normal threshold, while
  `inverseSquareSingleReverseAccumulatorFrom_le_of_le_steps` and
  `inverseSquareSingleReverseTenPowNineHighPrefixState_prefix_le_highPrefix`
  bound every earlier rounded prefix state by the final high-prefix state.
  Consequently
  `inverseSquareSingleReverseTenPowNineHighPrefixStep_exactInput_finiteNormalRange`
  proves the exact input to every high-prefix rounded addition is finite-normal,
  and `inverseSquareSingleReverseTenPowNineHighPrefixStep_standardModel_lt`
  gives a quantified standard-model factor
  `fl(s + 1/k^2) = (s + 1/k^2) * (1 + delta)` with
  `|delta| < unitRoundoff` for all `j < 10^9 - 4096`.  This closes a
  reusable whole-prefix model bridge, not an enumeration of the prefix steps.
  The follow-up absolute-error forms
  `inverseSquareSingleReverseTenPowNineHighPrefixStep_abs_error_lt_unitRoundoff_mul_exactInput`
  and
  `inverseSquareSingleReverseTenPowNineHighPrefixStep_abs_error_lt_unitRoundoff_mul_coarse`
  turn this into `|fl(s+t)-(s+t)| < u*(s+t)` and then into the uniform coarse
  high-prefix bound `u*(1/2048 + 2^-24)`.
- D1 accumulated standard-model envelope closed:
  `inverseSquareSingleReverseTenPowNineHighPrefixStepStdError` and
  `inverseSquareSingleReverseTenPowNineHighPrefixStdErrorEnvelope` define the
  recursive sum of the local high-prefix standard-model errors, with
  nonnegativity lemmas for both.  The block theorem
  `inverseSquareSingleReverseTenPowNineHighPrefix_abs_error_le_stdErrorEnvelope`
  proves by induction that every rounded prefix differs from the exact prefix by
  at most this envelope, and
  `inverseSquareSingleReverseTenPowNineHighPrefixState_abs_error_le_stdErrorEnvelope`
  specializes it to the full `10^9, ..., 4097` high-prefix state.  The coarse
  uniform instantiation of this idea is now ruled out by
  `inverseSquareSingleReverseTenPowNineHighPrefix_coarseAccumulatedStdErrorGuard_not_sufficient`;
  the next D1 target is a sharper interval/cell certificate for the actual
  rounded high-prefix trace, not prefix-step enumeration.
- D1 standard-envelope transfer route closed:
  `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowMarginTarget_of_stdErrorEnvelope_le`
  and
  `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget_of_stdErrorEnvelope_lt`
  prove that a sharp bound on the existing recursive high-prefix envelope is
  enough to discharge the closed-window D1 target or the stricter finite-cell
  D1 target.  The membership bridges
  `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_stdErrorEnvelope_le_candidateWindowMargin`
  and
  `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_stdErrorEnvelope_lt_cellGuardMargin`,
  together with the printed-value wrappers
  `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_stdErrorEnvelope_le_candidateWindowMargin_closed`
  and
  `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_stdErrorEnvelope_lt_cellGuardMargin_closed`,
  connect such a sharpened envelope bound directly to Higham's printed reverse
  value.  This does not close D1: the remaining mathematical target is proving
  one of those sharp high-prefix envelope/cell bounds, not using the known
  coarse accumulated envelope.
- D1 high-prefix `8192` split foothold closed:
  `inverseSquareTerm_le_two_pow_neg_26_of_ge_8192` proves the sharper binade
  term-size fact `1/k^2 <= 2^-26` for all `k >= 8192`.
  `inverseSquareReverseTenPowNineHighPrefix_index_ge_8192` and
  `inverseSquareTerm_le_two_pow_neg_26_of_reverse_ten_pow_nine_high_binade`
  specialize this to the earlier `10^9, ..., 8193` high-prefix block.  The
  structural split theorems
  `inverseSquareSingleReverseTenPowNineHighPrefixState_split_8192` and
  `inverseSquareExactReverseTenPowNineHighPrefix_split_8192` rewrite the
  rounded and exact high-prefix states as the earlier block followed by the
  final high-prefix binade `8192, ..., 4097`.  This creates a blockwise
  interval route for D1.  The same route now also has the tighter start-box
  bounds
  `inverseSquareExactReverseTenPowNineHighPrefixBefore8192_le_inv_8192` and
  `inverseSquareSingleReverseTenPowNineHighPrefixBefore8192_le_inv_4096`,
  proving that the exact earlier-block mass is at most `1/8192` and the
  rounded earlier-block state is at most `1/4096`.  The companion final-binade
  budgets `inverseSquareExactReverseBinade8192To4097_le_inv_8192` and
  `inverseSquareSingleReverseBinade8192To4097_le_start_add_inv_4096` prove that
  the exact `8192, ..., 4097` mass is at most `1/8192`, and that this whole
  rounded binade increases any finite binary32 start by at most `1/4096`.
  The exact earlier-block start-window dependency is now closed as well:
  `inverseSquareSingleReverseHighPrefixBefore8192WindowLower` and
  `inverseSquareSingleReverseHighPrefixBefore8192WindowUpper` define the
  binary32 start window feeding the final high-prefix binade, and
  `inverseSquareExactReverseTenPowNineHighPrefixBefore8192_mem_startWindow`
  proves by telescoping, without enumerating the `10^9, ..., 8193` block, that
  the exact earlier-block mass lies in that window.  The compact final-binade
  route is now closed, so the remaining block route is the rounded
  earlier-block membership in the same start window.
  The same-exponent tail data for that final-binade map is now closed:
  `inverseSquareSingleReverseHighBinade8190To4097Prefix_eq` proves that the
  scaled mantissa increment total for `8190^{-2}, ..., 4097^{-2}` at scale
  `q = 37` is `8385036`, and
  `inverseSquareSingleReverseHighBinade8190To4097WindowEndpointCertificateBool_eq_true`
  with
  `inverseSquareSingleReverseHighBinade8190To4097WindowEndpointCertificate`
  supplies the kernel-checked endpoint-safety certificate for the whole
  4094-step same-exponent tail.  The final-binade window map is now closed:
  `inverseSquareSingleReverseHighBinadeBefore8192Window_round_8192_step_mem_after8192Window`
  and
  `inverseSquareSingleReverseHighBinadeAfter8192Window_round_8191_step_mem_after8191Window`
  package the two boundary additions, while
  `inverseSquareSingleReverseHighBinadeTailWindow_prefix_mem` consumes the
  checked tail certificate.  The composed theorem
  `inverseSquareSingleReverseHighBinade8192To4097WindowMapsToCandidate_closed`
  maps every certified pre-binade start-window value through
  `8192^{-2}, ..., 4097^{-2}` into the high-prefix candidate window.  The bridge
  `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_before8192StartWindow`
  reduces candidate-window membership to the single still-open rounded
  earlier-block proposition
  `inverseSquareSingleReverseTenPowNineHighPrefixBefore8192InStartWindow`.
  A focused follow-up pass kept the blocker at exactly this theorem but reduced
  the equality route to a concrete named target: Lean now defines
  `inverseSquareSingleReverseTenPowNineHighPrefixBefore8192Candidate`
  (`0x38fff94f`), proves
  `inverseSquareSingleReverseTenPowNineHighPrefixBefore8192Candidate_mem_startWindow`,
  and proves
  `inverseSquareSingleReverseTenPowNineHighPrefixBefore8192InStartWindow_of_eq_candidate`.
  The remaining equality proposition is
  `inverseSquareSingleReverseTenPowNineHighPrefixBefore8192EqCandidate`.  The
  generic accumulated-error route is still too coarse for this row: the
  available standard-model and two-times-exact envelopes are structural
  sanity bounds, but their radii exceed the few-thousand-ulp start-window slack.
  The next viable route is therefore a dyadic finite-endpoint interval
  invariant for the rounded `10^9, ..., 8193` block, using symbolic/telescoping
  envelopes and nearest-rounding finite endpoint containment, not a
  `List.range (10^9 - 8192)` certificate and not per-step theorem expansion.
  A focused dependency pass has now closed the reusable no-change half-ulp
  bridge
  `inverseSquareSingleForwardStep_normalizedValue_eq_self_of_scaled_half_ulp_at_scale`:
  in any positive IEEE-single exponent band encoded by `q`, if `2^q < k^2`,
  then adding `1/k^2` rounds back to the same normalized state.  This supplies
  the missing local rule for compressed high-prefix bands where many terms are
  too small to move the accumulator, but it still has to be composed into the
  finite-endpoint invariant for `inverseSquareSingleReverseTenPowNineHighPrefixBefore8192EqCandidate`.
  The route guard
  `inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound_lt_inv_4096`
  proves that even the larger strict finite-cell D1 margin is smaller than
  this coarse `1/4096` increment budget, so these theorems are structural
  high-prefix data, not a low-index suffix replay and not by themselves a proof
  of candidate-window membership.
- D1 finite-cell guard route closed:
  `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_cellGuard`
  proves that
  `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuard`
  implies candidate-window membership, using finite-grid adjacency and the
  finite-system foothold.  The final wrapper
  `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_candidateWindowCellGuard_closed`
  reduces D1 to the two strict guard inequalities, not to any enumeration of
  suffix cases.
- D1 strict finite-cell margin route closed:
  `inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound`
  defines a fully explicit predecessor/successor-cell absolute-error radius
  around the exact high-prefix mass.  Its nonnegativity theorem,
  strict positivity theorem
  `inverseSquareSingleReverseHighPrefixCandidateWindowCellGuardMarginShiftedLowerBound_pos`,
  `inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound_le_cellGuardMarginShiftedLowerBound`,
  the strict comparison
  `inverseSquareSingleReverseHighPrefixCandidateWindowMarginShiftedLowerBound_lt_cellGuardMarginShiftedLowerBound`,
  the target bridge
  `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget_of_candidateWindowMarginTarget`,
  exact-prefix bridge
  `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget_of_eq_exact`,
  `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuard_of_abs_error_lt_cellGuardMarginShiftedLowerBound`,
  `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow_of_abs_error_lt_cellGuardMarginShiftedLowerBound`,
  the candidate consistency check
  `inverseSquareSingleReverseTenPowNineHighPrefixCandidate_abs_error_lt_cellGuardMarginShiftedLowerBound`,
  and
  `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_cellGuardMarginTarget_closed`
  show that one strict high-prefix absolute-error certificate against this
  larger cell margin closes the printed-value theorem.
- D1 consistency check closed:
  `inverseSquareSingleReverseTenPowNineHighPrefixCandidate_abs_error_le_candidateWindowMarginShiftedLowerBound`
  proves that the observed high-prefix candidate itself satisfies this explicit
  margin, and
  `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowMarginTarget_of_eq_candidate`
  proves that the older equality-to-candidate route implies the named target.
  The parallel guard theorem
  `inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuard_of_eq_candidate`
  proves that the same equality-to-candidate route also implies the finite-cell
  guard.
- D2: closed. Remaining before-`4` window suffix map:
  `inverseSquareSingleReverseBefore4WindowMapsToPrinted_closed`.
- D2a: closed full arbitrary-start same-exponent whole-window band map:
  `inverseSquareSingleReverseAfter4095Band4094ToBefore2048Window_closed`.
- D2a.0: closed endpoint propagation for that band:
  `inverseSquareSingleReverseAfter4095Band4094To2049WindowEndpointCertificate`
  plus the lower/upper endpoint equalities.
- D2a.1: closed generic midpoint-exclusion infrastructure for the interior
  lift, now threaded through the `2046`-step prefix induction by
  `inverseSquareSingleReverseAfter4095BandWindow_prefix_mem`.
- D2.1: closed first exact-add interval shift:
  `inverseSquareSingleReverseCandidateWindow_add_4096_term_mem_after4096Window`.
- D2.2: closed local finite round-to-even interval enclosure after the first
  suffix addition:
  `inverseSquareSingleReverseCandidateWindow_round_4096_step_mem_after4096Window`.
- D2.3: closed before-`2048` boundary and post-`2048` band-window propagation:
  `inverseSquareSingleReverseBefore2048WindowMapsToPrinted_of_before1024Window`.
- D2.4: closed before-`1024` boundary and post-`1024` band-window propagation:
  `inverseSquareSingleReverseBefore1024WindowMapsToPrinted_of_before512Window`.
- D2.5: closed before-`512` boundary and post-`512` band-window propagation:
  `inverseSquareSingleReverseBefore512WindowMapsToPrinted_of_before256Window`.
- D2.6: closed before-`256` boundary and post-`256` band-window propagation:
  `inverseSquareSingleReverseBefore256WindowMapsToPrinted_of_before128Window`.
- D2.7: closed before-`128` boundary and post-`128` band-window propagation:
  `inverseSquareSingleReverseBefore128WindowMapsToPrinted_of_before64Window`.
- D2.8: closed before-`64` boundary and post-`64` band-window propagation:
  `inverseSquareSingleReverseBefore64WindowMapsToPrinted_of_before32Window`.
- D2.9: closed before-`32` boundary and post-`32` band-window propagation:
  `inverseSquareSingleReverseBefore32WindowMapsToPrinted_of_before16Window`.
- D2.10: closed before-`16` boundary and post-`16` band-window propagation:
  `inverseSquareSingleReverseBefore16WindowMapsToPrinted_of_before8Window`.
- D2.11: closed before-`8` boundary and post-`8` band-window propagation:
  `inverseSquareSingleReverseBefore8WindowMapsToPrinted_of_before4Window`.
- D2.12: closed final before-`4` whole-window suffix propagation through the
  explicit `4^{-2}, 3^{-2}, 2^{-2}, 1^{-2}` additions by
  `inverseSquareSingleReverseBefore4WindowMapsToPrinted_closed`.

## Non-Enumeration Policy

Do not prove the final `4096` suffix steps one by one. The concrete candidate
suffix is already compressed into chunk certificates. Further work on the
whole-window route should use endpoint windows, binades, nearest-even interval
lemmas, and chunk certificates.

## Current Validation

The latest focused validation is recorded in
`docs/CHAPTER01_FULL_FORMALIZATION_LEDGER.md`. The remaining reverse-summation
blocker is not a low-index case split; it is the candidate-window prefix
membership theorem `inverseSquareSingleReverseTenPowNineHighPrefixInCandidateWindow`,
or equivalently one of its compact sufficient targets such as
`inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuardMarginTarget`,
`inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowMarginTarget`, or
`inverseSquareSingleReverseTenPowNineHighPrefixCandidateWindowCellGuard`.  The
standard-envelope bridge also shows that it would suffice to prove the existing
recursive envelope is below the closed-window margin or strictly below the
larger finite-cell margin, but the known coarse envelope is explicitly
insufficient.
