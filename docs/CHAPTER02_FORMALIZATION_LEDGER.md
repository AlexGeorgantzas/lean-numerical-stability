# Higham Chapter 2 Formalization Ledger

Audit date: 2026-06-11

Source audited: `References/Chapter02_full.pdf` (27 pages).  The exact path
`references/Chapter02.pdf` was not present in the workspace; the local Chapter 2
source is `References/Chapter02_full.pdf`.

Text spine: `/private/tmp/chapter02_full.txt`, produced by
`pdftotext -layout References/Chapter02_full.pdf /private/tmp/chapter02_full.txt`.
Line numbers below refer to that extracted text.  Representative formula pages
were rendered with `pdftoppm` and inspected for formulas lost by text extraction,
notably Theorem 2.3 and equation (2.5).

Gate status: FAIL.  Chapter 2 is not fully and faithfully end-to-end
formalized.  The repository already has the abstract standard arithmetic model
(2.4), this audit added the algebraic inverse relative-error surface for
Theorem 2.3/equation (2.5), and the continuation pass added a finite-format
vocabulary for §2.1/C2.5 plus per-exponent normalized range, exact normalized
endpoint values, the global finite-normalized magnitude range, basic
subnormal-value and near-zero equal-spacing facts, same-exponent
successor-spacing, exponent-boundary successor-spacing, a list-based
positional digit-string representation equivalent to the integer mantissa form,
and the full real-order normalized-adjacency version of Lemma 2.1.  In particular,
`adjacentNormalized_of_realOrderAdjacentNormalized` proves the converse from
arbitrary real-order adjacency back to the structural adjacency cases, and
`realOrderAdjacentNormalized_spacing_bounds_left` proves the displayed
`beta^(-1) eps_M |x|`/`eps_M |x|` bounds for arbitrary real-order adjacent
normalized endpoints, same-exponent signed fixed-bin floor bracketing/nearest
rounding, exponent-boundary signed bracketing/nearest rounding with source
power endpoint adapters, signed one-exponent power-slice wrappers, and global
nonzero nearest-rounding existence for the unbounded normalized system `G`.
Finite zero rounding, finite range/overflow/underflow classification
predicates for outputs of the finite nearest-rounding relation, and the
non-strict and strict finite-normal-range relation versions of Theorem 2.2 and
the non-strict Theorem 2.3 inverse relation are now proved.  The
finite-normal-range surfaces now also have the source-style noncomputable
arbitrary choice function `finiteNormalFl`, with strict forward and non-strict
inverse relative-error witnesses, and the proof-carrying finite-normal
round-away choice `finiteNormalRoundAway`, with explicit selector evidence,
Higham's strict forward witness, and the inverse relative-error witness.  The IEEE
single/double parameter tuples from lines 193--200 are now recorded as
`ieeeSingleFormat`/`ieeeDoubleFormat`, including their displayed unit-roundoff
values.
Full operation-level underflow/IEEE exception behavior, IEEE semantics,
guard-digit theorems, and Chapter 2 problems remain open.  The additive
underflow model (2.8) now has its algebraic witness predicates, branch
constructors, gradual/flush-to-zero eta-bound constants, normal-range
finite round-to-even branch wrappers, and the non-strict gradual-underflow
absolute-error/additive branch for the source-facing finite round-to-even
selector and operation/square-root wrappers.  The
finite-normal round-away and round-to-even source choices are proved, the total
arbitrary finite nearest choice `finiteNearestFl` covers relation-level
underflow, normal, and overflow nearest existence, and the source-facing total
finite round-away selector `finiteRoundAway` now combines a floor-based
underflow round-away branch, finite-normal adjacent-bracket round-away, and
overflow saturation.  The source-facing total finite round-to-even selector
`finiteRoundToEven` now combines a subnormal-lattice tie-to-even underflow
branch, finite-normal adjacent-bracket tie-to-even, and overflow saturation,
and proves nearest finite rounding for every real input plus the strict forward
and inverse relative-error witnesses on finite-normal inputs.  The local
adjacent-bracket directed selectors `adjacentRoundTowardNegative`,
`adjacentRoundTowardPositive`, and `adjacentRoundTowardZero` now fix exact
endpoints, otherwise choose the lower endpoint, upper endpoint, or
sign-dependent toward-zero endpoint of an ordered adjacent normalized bracket,
with representability and one-sided/order facts.  They are the local foundation
for finite directed rounding; the finite-normal source-evidence selectors
`finiteNormalRoundTowardNegative`, `finiteNormalRoundTowardPositive`, and
`finiteNormalRoundTowardZero` now lift them through normal-range exponent-slice
evidence with unbounded-normalized representability and one-sided/toward-zero
facts.  The total finite directed selectors `finiteRoundTowardNegative`,
`finiteRoundTowardPositive`, and `finiteRoundTowardZero` now add
subnormal-lattice underflow branches, finite-normal directed branches, finite
overflow saturation, and the finite mode dispatcher `finiteRoundToMode`.  The
square-root mode dispatcher `finiteRoundToModeSqrt` now reuses the same
finite selector on `Real.sqrt x`.  The ordinary
finite, non-exceptional operation bridge `finiteRoundToEvenOp` now rounds
`BasicOp.exact` by `finiteRoundToEven` and proves the strict standard-model
form when the exact operation result is finite-normal, and exactness when the
exact operation result is finite representable.  The finite left-add-zero
side condition is closed by `finiteRoundToEvenOp_add_zero_of_finiteSystem`.
`finiteRoundToEvenSqrt` does the same for nonnegative square-root inputs whose
exact square root is finite-normal, and is exact when the exact square root is
finite representable.  The C2.20 eta-bound identity
`gradualUnderflowEtaBound_eq_half_minSubnormalMagnitude` proves that Higham's
gradual-underflow `u * alpha` bound is half the subnormal spacing, and
`finiteRoundToEven_additiveUnderflowModel_underflow_branch_of_finiteUnderflowRange`
packages the underflow branch with `delta = 0`.  The first IEEE-facing result
vocabulary is also now explicit: rounding modes, exception flags, finite/
infinite/NaN values, and operation results are named, and the current
source-facing finite saturation/round-to-even/op/sqrt wrappers are embedded
only as finite, flag-free results.  The first IEEE overflow semantic predicate
and default-result constructor now record the mode-dependent overflow value and
the overflow/inexact flags for source-facing overflow-range inputs, and the
nearest/even primitive-operation wrapper dispatches overflow exact results to
that flagged IEEE result.  The mode-parameterized primitive-operation wrapper
`ieeeRoundToModeOpResult` plus the directed aliases now dispatch overflow exact
results through `ieeeOverflowValue` for all IEEE rounding modes and dispatch
finite underflow/no-flag exact results through `finiteRoundToModeOp` using the
mode-aware `ieeeUnderflowModeResult` predicate.  The nearest/even wrapper now
also dispatches underflow exact results to a finite rounded result with an
underflow flag, conditional inexact flag, and the existing additive underflow
model witness.  The corresponding square-root mode wrapper now dispatches real
square-root overflow exact results through the same mode-dependent overflow
table and finite underflow/no-flag exact results through
`finiteRoundToModeSqrt`; its nearest/even specialization carries the additive
underflow model witness.  The generic invalid-operation/NaN predicate and
square-root invalid-operation constructor are now explicit, and the square-root
mode wrapper dispatches negative real inputs to that invalid-operation result
for every mode.  The division-by-zero exception now has an input predicate, an
infinite-result/division-by-zero-flag predicate for finite nonzero divided
by modeled zero, signed `+0`/`-0` denominator infinity selectors, and an
ordinary modeled `finite 0` denominator default selector for positive and
negative finite numerators.  Primitive quiet-NaN propagation and invalid-operation special
inputs such as `0/0`, `0 * infinity`, `infinity * 0`, `infinity / infinity`,
and indeterminate infinity addition/subtraction now have IEEE-facing predicate
constructors.  The first IEEE-value square-root wrapper now also handles NaN,
positive infinity, and negative infinity special inputs explicitly.  The
IEEE-facing value layer now distinguishes positive and negative zero, proves
the modeled NaN unordered/unequal comparison facts, signed-zero comparison
equality, and predicate-level comparison completeness, and the square-root value wrapper preserves both signed zeros with no
flags.  None of these finite wrappers is a full IEEE operation.
The no-guard model (2.6a,b) now has a separate abstract predicate/structure
surface: add/sub use separate strict operand perturbations, mul/div retain the
strict relative-error model, and Higham's displayed three-bit binary
dropped-guard example is recorded as exact rational arithmetic with relative
error one.  This is not yet a guard-digit subtraction algorithm or the
Ferguson/Sterbenz exact-subtraction theorem.
The Ferguson/Sterbenz block now has an explicit theorem-surface interface:
normalized exponent representations model Higham's `e(x)`, the Ferguson
condition records exponent data for `x`, `y`, and `x-y`, and a
`guardDigitSubtractionModel` proves exact subtraction under that condition.
The source proof's first Ferguson reduction is now formalized: under that
condition the exponents of `x` and `y` differ by at most one, and the
normalized representation of `x-y` yields finite-format no-underflow and
no-overflow facts.  The next proof sentence is also formalized: the
Ferguson condition forces same-sign normalized representations for `x` and
`y`, and the exponent cases reduce to same exponent or a one-exponent
shift.  The raw aligned subtraction identities for the same exponent case
and the one-exponent-shift guard-digit case are also named.  The same-exponent
mantissa difference is proved to have at most `t` digits and to be unchanged by
the modeled `t`-digit coefficient rounding; the one-shift guard-aligned
coefficient, including its integer `beta*mHigh - mLow` form, is proved below the
normalized leading-digit threshold under both adjacent orientations, and the
direct positive Sterbenz adjacent-exponent branch now proves that this
coefficient is positive and below the `t`-digit mantissa bound under the ratio
condition and has a finite-system/exact finite round-to-even wrapper for that
positive adjacent-exponent branch.  The source
proof's `z1 = 0` sentence is now formalized as a zero leading digit for the
`t+1` guard word, with the trailing `t`-digit tail unchanged, and dropping that
zero guard digit with the original sign is proved to preserve the
adjacent-exponent subtraction value.  The branch cases are now packaged by
`guardDigitBranchSubtractionModel`, and a noncomputable evidence-selecting
`guardDigitBranchSubtractionRoutine` is proved to satisfy
`guardDigitSubtractionModel` under Ferguson's condition.  The branch-selected
value is also proved finite, using the derived same-exponent finite-difference
selector in the same-exponent branch, and the same-exponent/Ferguson-data cases
are connected to exact concrete finite round-to-even subtraction.  The remaining
Ferguson implementation gap is a fully executable digit-level or full IEEE
routine.  The Sterbenz ratio distance lemmas are now proved, and a one-digit decimal
counterexample shows that Sterbenz's ratio condition does not imply Ferguson's
exponent condition in general bases.  The same-exponent direct
representability branch is now split into two proved endpoints: if the exact
integer mantissa difference is already normalized, the exact subtraction result
is a finite normalized value; if one base shift makes that exact integer
difference normalized and exponent `e - 1` is in range, the exact subtraction
result is a finite normalized value at exponent `e - 1`; more generally, if
any finite radix-power shift makes the exact integer difference normalized and
the shifted exponent stays in range, the exact subtraction result is finite
normalized at that shifted exponent; at `emin`, if that difference is below the
normalized leading-digit threshold, the exact subtraction result is zero or
subnormal and therefore finite; and the same subnormal endpoint is now proved
after a finite radix-power shift lands at `emin`.  These cases are packaged by
`sameExponentFiniteDifferenceWitness`, whose wrapper proves finite-system
representability from exact zero, a normalized renormalization shift, or a
shifted `emin` subnormal endpoint.  The witness is now derived from
same-exponent normalized operand mantissas and an in-range exponent, giving a
source-facing finite-system theorem for same-exponent exact subtraction.  A
generic bounded-integer finite-system adapter now turns the direct positive
adjacent-exponent Sterbenz coefficient bound into finite representability and
exact concrete finite round-to-even subtraction for that branch.  Sterbenz's
ratio condition is now also proved symmetric and proved to force a one-exponent
gap for positive normalized operands; combining that gap with the same-exponent
and both adjacent-exponent branches proves finite representability and exact
concrete finite round-to-even subtraction for positive normalized operands with
in-range exponents, and a source-shaped wrapper lifts that result to
`normalizedSystem` operands.  The subnormal lattice branch is now also closed:
same-sign subnormal subtraction is finite, and the Sterbenz ratio condition
forces subnormal-system operands into the positive same-sign branch, giving
exact concrete finite round-to-even subtraction for all-subnormal Sterbenz
operands.  The mixed normal/subnormal branch is now closed by rewriting the
normal operand on the subnormal lattice and using Sterbenz's upper ratio bound
to keep the exact integer difference below the `t`-digit mantissa bound.  This
gives a direct source-facing finite-system all-case Sterbenz theorem and exact
concrete finite round-to-even subtraction for all finite Sterbenz operands.  The
remaining Sterbenz work is the fully executable digit-level/full IEEE
subtraction operation theorem.

## Closed During This Audit

Lean file:

- `LeanFpAnalysis/FP/Analysis/Counting.lean`
- `LeanFpAnalysis/FP/Analysis/Error.lean`
- `LeanFpAnalysis/FP/Analysis/FloatingPointArithmetic.lean`
- `LeanFpAnalysis/FP/Analysis/Heron.lean`
- `LeanFpAnalysis/FP/Analysis/Problem2_2.lean`
- `LeanFpAnalysis/FP/Analysis/Problem2_4.lean`
- `LeanFpAnalysis/FP/Analysis/Problem2_5.lean`
- `LeanFpAnalysis/FP/Analysis/Problem2_7.lean`

New theorem surface:

- `FloatingPointFormat.normalizedExponentParameterCount`
- `FloatingPointFormat.normalizedMantissaParameterCount`
- `FloatingPointFormat.subnormalMantissaParameterCount`
- `FloatingPointFormat.signedParameterCount`
- `FloatingPointFormat.normalizedNumberParameterCount`
- `FloatingPointFormat.subnormalNumberParameterCount`
- `FloatingPointFormat.normalizedMantissaParameterCount_eq_beta_pow_sub`
- `FloatingPointFormat.subnormalMantissaParameterCount_eq_beta_pow_sub_one`
- `FloatingPointFormat.normalizedNumberParameterCount_eq_problem2_1_formula`
- `FloatingPointFormat.subnormalNumberParameterCount_eq_problem2_1_formula`
- `FloatingPointFormat.subnormalValue_eq_iff_sign_mantissa`
- `FloatingPointFormat.problem2_1_ieeeSingle_normalizedNumberParameterCount`
- `FloatingPointFormat.problem2_1_ieeeSingle_subnormalNumberParameterCount`
- `FloatingPointFormat.problem2_1_ieeeDouble_normalizedNumberParameterCount`
- `FloatingPointFormat.problem2_1_ieeeDouble_subnormalNumberParameterCount`
- `FloatingPointFormat.problem2_2_lemma2_1_spacing_bounds_left`
- `FloatingPointFormat.problem2_2_lemma2_1_spacing_bounds_right`
- `FloatingPointFormat.problem2_2_lemma2_1_spacing_bounds`
- `FloatingPointFormat.problem2_3_singleToDoubleMantissaScale`
- `FloatingPointFormat.problem2_3_ieeeSingle_normalizedValue_eq_ieeeDouble_scaledMantissa`
- `FloatingPointFormat.problem2_3_ieeeSingle_minNormal_eq_ieeeDouble_minNormal`
- `FloatingPointFormat.problem2_3_sameExponentInteriorDoubleMantissas`
- `FloatingPointFormat.problem2_3_sameExponentInteriorDoubleMantissas_card`
- `FloatingPointFormat.problem2_3_sameExponentInteriorDoubleMantissas_mem_iff`
- `FloatingPointFormat.problem2_3_ieeeDouble_sameExponent_between_iff_mem`
- `FloatingPointFormat.problem2_3_ieeeDouble_sameExponent_negative_between_iff_mem`
- `FloatingPointFormat.problem2_3_ieeeSingle_exponentInRange_ieeeDouble`
- `FloatingPointFormat.problem2_3_sameExponentInteriorDoubleMantissa_normalized`
- `FloatingPointFormat.problem2_3_sameExponentInteriorDoubleMantissa_normalized_of_mem`
- `FloatingPointFormat.problem2_3_ieeeDouble_normalized_sameExponent_positive_between_mem`
- `FloatingPointFormat.problem2_3_ieeeDouble_minNormalMagnitude_lt_ieeeSingle_normalized_false`
- `FloatingPointFormat.problem2_3_ieeeSingle_normalized_true_lt_neg_ieeeDouble_minNormalMagnitude`
- `FloatingPointFormat.problem2_3_ieeeDouble_between_adjacent_ieeeSingle_sameExponent`
- `FloatingPointFormat.problem2_3_ieeeDouble_between_adjacent_ieeeSingle_sameExponent_signed`
- `FloatingPointFormat.problem2_3_boundaryInteriorDoubleMantissas`
- `FloatingPointFormat.problem2_3_boundaryInteriorDoubleMantissas_card`
- `FloatingPointFormat.problem2_3_boundaryInteriorDoubleMantissas_mem_iff`
- `FloatingPointFormat.problem2_3_ieeeDouble_boundary_between_iff_mem`
- `FloatingPointFormat.problem2_3_ieeeDouble_boundary_negative_between_iff_mem`
- `FloatingPointFormat.problem2_3_boundaryInteriorDoubleMantissa_normalized`
- `FloatingPointFormat.problem2_3_boundaryInteriorDoubleMantissa_normalized_of_mem`
- `FloatingPointFormat.problem2_3_ieeeDouble_normalized_boundary_positive_between_mem`
- `FloatingPointFormat.problem2_3_ieeeDouble_normalized_boundary_signed_between_mem`
- `FloatingPointFormat.problem2_3_ieeeDouble_between_adjacent_ieeeSingle_boundary`
- `FloatingPointFormat.problem2_3_ieeeDouble_between_adjacent_ieeeSingle_boundary_signed`
- `FloatingPointFormat.problem2_3_smallestSubnormalInteriorDoubleMantissas`
- `FloatingPointFormat.problem2_3_smallestSubnormalInteriorDoubleMantissas_card`
- `FloatingPointFormat.problem2_3_smallestSubnormalInteriorDoubleMantissas_mem_iff`
- `FloatingPointFormat.problem2_3_ieeeSingle_one_subnormalMantissa`
- `FloatingPointFormat.problem2_3_ieeeSingle_two_subnormalMantissa`
- `FloatingPointFormat.problem2_3_smallestSubnormalInteriorDoubleMantissa_normalized`
- `FloatingPointFormat.problem2_3_subnormalBlockScale`
- `FloatingPointFormat.problem2_3_subnormalBlockInteriorDoubleMantissas`
- `FloatingPointFormat.problem2_3_subnormalBlockInteriorDoubleMantissas_card`
- `FloatingPointFormat.problem2_3_subnormalBlockInteriorDoubleMantissas_mem_iff`
- `FloatingPointFormat.problem2_3_ieeeDouble_subnormalBlock_between_iff_mem`
- `FloatingPointFormat.problem2_3_ieeeDouble_subnormalBlock_negative_between_iff_mem`
- `FloatingPointFormat.problem2_3_subnormalBlockInteriorDoubleMantissa_normalized`
- `FloatingPointFormat.problem2_3_subnormalBlockInteriorDoubleMantissa_normalized_of_mem`
- `FloatingPointFormat.problem2_3_ieeeDouble_between_ieeeSingle_positive_subnormal_block`
- `FloatingPointFormat.problem2_3_ieeeDouble_between_ieeeSingle_subnormal_block_signed`
- `FloatingPointFormat.problem2_3_ieeeDouble_between_first_two_ieeeSingle_subnormals`
- `FloatingPointFormat.problem2_3_ieeeSingle_subnormalValue_eq_ieeeDouble_scaledMantissa`
- `FloatingPointFormat.problem2_3_ieeeSingle_subnormalMantissa_of_block`
- `FloatingPointFormat.problem2_3_exists_subnormalBlock_of_ieeeSingle_subnormalMantissa`
- `FloatingPointFormat.problem2_3_ieeeDouble_minNormalMagnitude_lt_ieeeSingle_subnormal_false`
- `FloatingPointFormat.problem2_3_ieeeSingle_subnormal_true_lt_neg_ieeeDouble_minNormalMagnitude`
- `FloatingPointFormat.Problem2_3IeeeSingleAdjacentGap`
- `FloatingPointFormat.problem2_3_adjacentSingleGapInteriorDoubleMantissas`
- `FloatingPointFormat.problem2_3_adjacentSingleGapInteriorCount`
- `FloatingPointFormat.problem2_3_adjacentSingleGapLeftValue`
- `FloatingPointFormat.problem2_3_adjacentSingleGapRightValue`
- `FloatingPointFormat.problem2_3_exists_adjacentSingleGap_of_ieeeSingle_subnormalMantissa`
- `FloatingPointFormat.problem2_3_adjacentSingleGapDoubleValue`
- `FloatingPointFormat.problem2_3_ieeeDouble_normalized_sameExponent_signed_between_mem`
- `FloatingPointFormat.problem2_3_ieeeDouble_finiteSystem_sameExponent_signed_between_exists_mem`
- `FloatingPointFormat.problem2_3_ieeeDouble_finiteSystem_boundary_signed_between_exists_mem`
- `FloatingPointFormat.problem2_3_ieeeDouble_normalized_subnormalBlock_positive_between_mem`
- `FloatingPointFormat.problem2_3_ieeeDouble_normalized_subnormalBlock_signed_between_mem`
- `FloatingPointFormat.problem2_3_ieeeDouble_finiteSystem_subnormalBlock_signed_between_exists_mem`
- `FloatingPointFormat.problem2_3_adjacentSingleGap_finiteSystem_between_exists_mem`
- `FloatingPointFormat.problem2_3_adjacentSingleGapInteriorDoubleMantissas_card`
- `FloatingPointFormat.problem2_3_adjacentSingleGap_between_iff_mem`
- `FloatingPointFormat.problem2_3_adjacentSingleGapDoubleValue_finiteSystem_of_mem`
- `FloatingPointFormat.problem2_4_theorem2_3_nearest_finite`
- `FloatingPointFormat.problem2_4_theorem2_3_finiteNormalFl`
- `FloatingPointFormat.problem2_4_theorem2_3_finiteRoundToEven`
- `FloatingPointFormat.problem2_5_binaryOneTenthTerm`
- `FloatingPointFormat.problem2_5_binaryOneTenth_hasSum`
- `FloatingPointFormat.problem2_5_binaryOneTenth_tsum`
- `FloatingPointFormat.problem2_5_ieeeSingle_oneTenth_finiteNormalRange`
- `FloatingPointFormat.problem2_5_ieeeSingle_roundToEven_oneTenth`
- `FloatingPointFormat.problem2_5_ieeeSingle_oneTenth_relative_error`
- `FloatingPointFormat.integerIntervalRepresentable`
- `FloatingPointFormat.problem2_6_ieeeSingle_integerIntervalRepresentable_two_pow_24`
- `FloatingPointFormat.problem2_6_ieeeDouble_integerIntervalRepresentable_two_pow_53`
- `FloatingPointFormat.problem2_6_ieeeSingle_two_pow_24_add_one_not_finiteSystem`
- `FloatingPointFormat.problem2_6_ieeeDouble_two_pow_53_add_one_not_finiteSystem`
- `FloatingPointFormat.problem2_6_ieeeSingle_largest_integer_interval`
- `FloatingPointFormat.problem2_6_ieeeDouble_largest_integer_interval`
- `FloatingPointFormat.nearestAdjacentRoundToEven_eq_left_endpoint`
- `FloatingPointFormat.nearestAdjacentRoundToEven_eq_right_endpoint`
- `FloatingPointFormat.sourceRoundToEvenEvidence_eq_self_of_unboundedNormalizedSystem`
- `FloatingPointFormat.sourceRoundToEvenEvidence_eq_nearest_of_realOrderAdjacent_between`
- `FloatingPointFormat.sourceRoundToEvenEvidence_unique`
- `FloatingPointFormat.finiteNormalRoundToEven_eq_of_sourceRoundToEvenEvidence`
- `FloatingPointFormat.evenMantissa_succ_iff_not_evenMantissa`
- `FloatingPointFormat.evenMantissa_iff_not_evenMantissa_succ`
- `FloatingPointFormat.evenMantissa_minNormalMantissa_of_even_beta`
- `FloatingPointFormat.not_evenMantissa_maxNormalMantissa_of_even_beta`
- `FloatingPointFormat.evenMantissa_minNormalMantissa_iff_not_evenMantissa_maxNormalMantissa_of_even_beta`
- `FloatingPointFormat.evenMantissa_maxNormalMantissa_iff_not_evenMantissa_minNormalMantissa_of_even_beta`
- `FloatingPointFormat.nearestAdjacentRoundToEven_neg_of_even_right_iff_not_even_left`
- `FloatingPointFormat.realOrderAdjacentNormalized_neg_ordered`
- `FloatingPointFormat.realOrderAdjacentNormalized_right_mantissa_parity`
- `FloatingPointFormat.sourceRoundToEvenEvidence_neg`
- `FloatingPointFormat.finiteNormalRoundToEven_neg`
- `FloatingPointFormat.finiteRoundToEven_neg_of_finiteNormalRange`
- `FloatingPointFormat.finiteRoundToEven_neg`
- `FloatingPointFormat.finiteRoundToEvenOp_add_comm`
- `FloatingPointFormat.finiteRoundToEvenOp_mul_comm`
- `FloatingPointFormat.problem2_7_statement2_sub_sign_symmetry_of_exact_finiteSystem`
- `FloatingPointFormat.problem2_7_statement2_sub_sign_symmetry_of_not_finiteNormalRange`
- `FloatingPointFormat.problem2_7_statement2_sub_sign_symmetry`
- `FloatingPointFormat.finiteRoundToEvenOp_add_self_eq_mul_two`
- `FloatingPointFormat.finiteRoundToEvenOp_half_mul_eq_div_two`
- `FloatingPointFormat.problem2_7_statement5_add_associativity_false`
- `FloatingPointFormat.problem2_7_statement6_midpoint_strict_between_false`
- `FloatingPointFormat.problem2_8_decimal_midpoint_strict_between_violated`
- `FloatingPointFormat.decimalOneDigitThreeExponent_midpoint_one_two_rounds_to_two`
- `FloatingPointFormat.decimalOneDigitThreeExponentFormat_three_halves_not_finiteSystem`
- `FloatingPointFormat.decimalOneDigitThreeExponent_sub_two_one_exact`
- `FloatingPointFormat.decimalOneDigitThreeExponent_div_one_two_exact`
- `FloatingPointFormat.decimalOneDigitThreeExponent_add_one_one_half_rounds_to_two`
- `FloatingPointFormat.problem2_8_finiteRoundToEven_guarded_sequence_counterexample`
- `FloatingPointFormat.problem2_8_guarded_sequence_counterexample_missing_midpoint_finiteSystem`
- `FloatingPointFormat.problem2_8_exact_guarded_midpoint_strict_between`
- `FloatingPointFormat.problem2_8_guarded_exact_operation_sequence_eq_exact_midpoint`
- `FloatingPointFormat.problem2_8_guarded_exact_operation_sequence_strict_between`
- `FloatingPointFormat.problem2_8_guarded_sequence_eq_exact_midpoint_of_finite_midpoint_steps`
- `FloatingPointFormat.problem2_8_guarded_sequence_strict_between_of_finite_midpoint_steps`
- `FloatingPointFormat.problem2_8_guarded_sequence_strict_between_of_sterbenz_subtraction`
- `FloatingPointFormat.problem2_10_displayed_denominator_eq_power_sum`
- `FloatingPointFormat.problem2_10_powerOfTwo_numerator_kahan_hypotheses`
- `FloatingPointFormat.problem2_10_negative_powerOfTwo_numerator_kahan_hypotheses`
- `FloatingPointFormat.problem2_10_allowableDenominator`
- `FloatingPointFormat.problem2_10_allowableDenominator_of_nat_power_sum`
- `FloatingPointFormat.problem2_10_allowableDenominator_ne_zero`
- `FloatingPointFormat.problem2_10_kahan_integer_hypotheses_of_allowableDenominator`
- `FloatingPointFormat.problem2_10_powerOfTwo_numerator_kahan_hypotheses_of_allowableDenominator`
- `FloatingPointFormat.problem2_10_negative_powerOfTwo_numerator_kahan_hypotheses_of_allowableDenominator`
- `FloatingPointFormat.problem2_10_displayedAllowableDenominatorPrefix`
- `FloatingPointFormat.problem2_10_displayedAllowableDenominatorPrefix_allowable`
- `FloatingPointFormat.problem2_10_denominator_five_eq_power_sum`
- `FloatingPointFormat.problem2_10_five_allowableDenominator`
- `FloatingPointFormat.problem2_10_denominator_six_eq_power_sum`
- `FloatingPointFormat.problem2_10_six_allowableDenominator`
- `FloatingPointFormat.problem2_10_denominator_nine_eq_power_sum`
- `FloatingPointFormat.problem2_10_nine_allowableDenominator`
- `FloatingPointFormat.problem2_10_denominator_ten_eq_power_sum`
- `FloatingPointFormat.problem2_10_ten_allowableDenominator`
- `FloatingPointFormat.problem2_10_denominator_twelve_eq_power_sum`
- `FloatingPointFormat.problem2_10_twelve_allowableDenominator`
- `FloatingPointFormat.problem2_10_denominator_seventeen_eq_power_sum`
- `FloatingPointFormat.problem2_10_seventeen_allowableDenominator`
- `FloatingPointFormat.problem2_10_denominator_eighteen_eq_power_sum`
- `FloatingPointFormat.problem2_10_eighteen_allowableDenominator`
- `FloatingPointFormat.problem2_10_denominator_twenty_eq_power_sum`
- `FloatingPointFormat.problem2_10_twenty_allowableDenominator`
- `FloatingPointFormat.problem2_10_denominator_thirtythree_eq_power_sum`
- `FloatingPointFormat.problem2_10_thirtythree_allowableDenominator`
- `FloatingPointFormat.problem2_10_denominator_sixtyfive_eq_power_sum`
- `FloatingPointFormat.problem2_10_sixtyfive_allowableDenominator`
- `FloatingPointFormat.problem2_10_denominator_onehundredtwentynine_eq_power_sum`
- `FloatingPointFormat.problem2_10_onehundredtwentynine_allowableDenominator`
- `FloatingPointFormat.problem2_10_denominator_twohundredfiftyseven_eq_power_sum`
- `FloatingPointFormat.problem2_10_twohundredfiftyseven_allowableDenominator`
- `FloatingPointFormat.problem2_10_denominator_fivehundredthirteen_eq_power_sum`
- `FloatingPointFormat.problem2_10_fivehundredthirteen_allowableDenominator`
- `FloatingPointFormat.problem2_10_denominator_onethousandtwentyfive_eq_power_sum`
- `FloatingPointFormat.problem2_10_onethousandtwentyfive_allowableDenominator`
- `FloatingPointFormat.problem2_10_denominator_twothousandfortynine_eq_power_sum`
- `FloatingPointFormat.problem2_10_twothousandfortynine_allowableDenominator`
- `FloatingPointFormat.problem2_10_denominator_fourthousandninetyseven_eq_power_sum`
- `FloatingPointFormat.problem2_10_fourthousandninetyseven_allowableDenominator`
- `FloatingPointFormat.problem2_10_denominator_eightthousandonehundredninetythree_eq_power_sum`
- `FloatingPointFormat.problem2_10_eightthousandonehundredninetythree_allowableDenominator`
- `FloatingPointFormat.problem2_10_denominator_sixteenthousandthreehundredeightyfive_eq_power_sum`
- `FloatingPointFormat.problem2_10_sixteenthousandthreehundredeightyfive_allowableDenominator`
- `FloatingPointFormat.problem2_10_denominator_thirtytwothousandsevenhundredsixtynine_eq_power_sum`
- `FloatingPointFormat.problem2_10_thirtytwothousandsevenhundredsixtynine_allowableDenominator`
- `FloatingPointFormat.problem2_10_denominator_sixtyfivethousandfivehundredthirtyseven_eq_power_sum`
- `FloatingPointFormat.problem2_10_sixtyfivethousandfivehundredthirtyseven_allowableDenominator`
- `FloatingPointFormat.problem2_10_denominator_onehundredthirtyonethousandseventythree_eq_power_sum`
- `FloatingPointFormat.problem2_10_onehundredthirtyonethousandseventythree_allowableDenominator`
- `FloatingPointFormat.problem2_10_denominator_twohundredsixtytwothousandonehundredfortyfive_eq_power_sum`
- `FloatingPointFormat.problem2_10_twohundredsixtytwothousandonehundredfortyfive_allowableDenominator`
- `FloatingPointFormat.problem2_10_denominator_fivehundredtwentyfourthousandtwohundredeightynine_eq_power_sum`
- `FloatingPointFormat.problem2_10_fivehundredtwentyfourthousandtwohundredeightynine_allowableDenominator`
- `FloatingPointFormat.problem2_10_denominator_onemillionfortyeightthousandfivehundredseventyseven_eq_power_sum`
- `FloatingPointFormat.problem2_10_onemillionfortyeightthousandfivehundredseventyseven_allowableDenominator`
- `FloatingPointFormat.problem2_10_denominator_twomillionninetyseventhousandonehundredfiftythree_eq_power_sum`
- `FloatingPointFormat.problem2_10_twomillionninetyseventhousandonehundredfiftythree_allowableDenominator`
- `FloatingPointFormat.problem2_10_one_sixth_kahan_hypotheses`
- `FloatingPointFormat.problem2_10_negative_one_sixth_kahan_hypotheses`
- `FloatingPointFormat.problem2_10_one_tenth_kahan_hypotheses`
- `FloatingPointFormat.problem2_10_negative_one_tenth_kahan_hypotheses`
- `FloatingPointFormat.problem2_10_two_pow_succ_numerator_kahan_hypotheses_of_ten`
- `FloatingPointFormat.problem2_10_negative_two_pow_succ_numerator_kahan_hypotheses_of_ten`
- `FloatingPointFormat.problem2_10_two_pow_add_two_numerator_kahan_hypotheses_of_twelve`
- `FloatingPointFormat.problem2_10_negative_two_pow_add_two_numerator_kahan_hypotheses_of_twelve`
- `FloatingPointFormat.problem2_10_two_pow_succ_numerator_kahan_hypotheses_of_eighteen`
- `FloatingPointFormat.problem2_10_negative_two_pow_succ_numerator_kahan_hypotheses_of_eighteen`
- `FloatingPointFormat.problem2_10_two_pow_add_two_numerator_kahan_hypotheses_of_twenty`
- `FloatingPointFormat.problem2_10_negative_two_pow_add_two_numerator_kahan_hypotheses_of_twenty`
- `FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_nine`
- `FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_nine`
- `FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_seventeen`
- `FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_seventeen`
- `FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_thirtythree`
- `FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_thirtythree`
- `FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_sixtyfive`
- `FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_sixtyfive`
- `FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_onehundredtwentynine`
- `FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_onehundredtwentynine`
- `FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_twohundredfiftyseven`
- `FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_twohundredfiftyseven`
- `FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_fivehundredthirteen`
- `FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_fivehundredthirteen`
- `FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_onethousandtwentyfive`
- `FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_onethousandtwentyfive`
- `FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_twothousandfortynine`
- `FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_twothousandfortynine`
- `FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_fourthousandninetyseven`
- `FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_fourthousandninetyseven`
- `FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_eightthousandonehundredninetythree`
- `FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_eightthousandonehundredninetythree`
- `FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_sixteenthousandthreehundredeightyfive`
- `FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_sixteenthousandthreehundredeightyfive`
- `FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_thirtytwothousandsevenhundredsixtynine`
- `FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_thirtytwothousandsevenhundredsixtynine`
- `FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_sixtyfivethousandfivehundredthirtyseven`
- `FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_sixtyfivethousandfivehundredthirtyseven`
- `FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_onehundredthirtyonethousandseventythree`
- `FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_onehundredthirtyonethousandseventythree`
- `FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_twohundredsixtytwothousandonehundredfortyfive`
- `FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_twohundredsixtytwothousandonehundredfortyfive`
- `FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_fivehundredtwentyfourthousandtwohundredeightynine`
- `FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_fivehundredtwentyfourthousandtwohundredeightynine`
- `FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_onemillionfortyeightthousandfivehundredseventyseven`
- `FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_onemillionfortyeightthousandfivehundredseventyseven`
- `FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_twomillionninetyseventhousandonehundredfiftythree`
- `FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_twomillionninetyseventhousandonehundredfiftythree`
- `FloatingPointFormat.problem2_10_one_fifth_kahan_hypotheses`
- `FloatingPointFormat.problem2_10_negative_one_fifth_kahan_hypotheses`
- `FloatingPointFormat.problem2_10_two_fifth_kahan_hypotheses`
- `FloatingPointFormat.problem2_10_negative_two_fifth_kahan_hypotheses`
- `FloatingPointFormat.problem2_10_three_fifth_kahan_hypotheses`
- `FloatingPointFormat.problem2_10_negative_three_fifth_kahan_hypotheses`
- `FloatingPointFormat.problem2_10_three_mul_powerOfTwo_numerator_kahan_hypotheses_of_five`
- `FloatingPointFormat.problem2_10_negative_three_mul_powerOfTwo_numerator_kahan_hypotheses_of_five`
- `FloatingPointFormat.problem2_10_ieeeDouble_finiteSystem_five`
- `FloatingPointFormat.problem2_10_ieeeDouble_one_fifth_trace_finite_inputs`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_one_fifth_trace_finite_inputs`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_fifth_trace_finite_inputs`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_two_fifth_trace_finite_inputs`
- `FloatingPointFormat.problem2_10_ieeeDouble_three_fifth_trace_finite_inputs`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_three_fifth_trace_finite_inputs`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_le_maxFiniteMagnitude`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_three_finiteNormalRange`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_thirds_rounds_to_lower`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_thirds_mul_three_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_three_exact_mul_three_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_midpoint_below_two_pow_rounds_to_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_thirds_times_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_thirds_mul_three_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_three_exact_mul_three_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_midpoint_above_two_pow_rounds_to_neg_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_thirds_times_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_thirds_times_three`
- `FloatingPointFormat.problem2_10_finiteRoundToEven_div_mul_exact_of_finiteSystem`
- `FloatingPointFormat.problem2_10_ieeeDouble_zero_allowable_denominator_times_denominator'`
- `FloatingPointFormat.problem2_10_ieeeDouble_allowable_denominator_exact_quotient_trace`
- `FloatingPointFormat.problem2_10_ieeeDouble_oneFifth_rounds_to_upper`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_one_five`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_oneFifth_mul_five_above_one`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_one_five_exact_mul_five_above_one`
- `FloatingPointFormat.problem2_10_ieeeDouble_one_plus_two_pow_neg54_rounds_to_one`
- `FloatingPointFormat.problem2_10_ieeeDouble_one_fifth_times_five`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_one_five`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_oneFifth_mul_five_below_neg_one`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_one_five_exact_mul_five_below_neg_one`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_one_plus_two_pow_neg54_rounds_to_neg_one`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_one_fifth_times_five`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_one_fifth_times_five`
- `FloatingPointFormat.problem2_10_ieeeDouble_twoFifths_rounds_to_upper`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_five`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_twoFifths_mul_five_above_two`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_five_exact_mul_five_above_two`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_plus_two_pow_neg53_rounds_to_two`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_fifth_times_five`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_five`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_twoFifths_mul_five_below_neg_two`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_five_exact_mul_five_below_neg_two`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_two_plus_two_pow_neg53_rounds_to_neg_two`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_two_fifth_times_five`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_two_fifth_times_five`
- `FloatingPointFormat.problem2_10_ieeeDouble_threeFifths_rounds_to_lower`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_three_five`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_threeFifths_mul_five_below_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_three_five_exact_mul_five_below_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_three_minus_two_pow_neg53_rounds_to_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_three_fifth_times_five`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_three_five`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_threeFifths_mul_five_above_neg_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_three_five_exact_mul_five_above_neg_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_three_minus_two_pow_neg53_rounds_to_neg_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_three_fifth_times_five`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_three_fifth_times_five`
- `FloatingPointFormat.problem2_10_ieeeDouble_three_mul_two_pow_div_five_finiteNormalRange`
- `FloatingPointFormat.problem2_10_ieeeDouble_three_mul_two_pow_fifths_rounds_to_lower`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_three_mul_two_pow_five`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_three_mul_two_pow_fifths_mul_five_below`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_three_mul_two_pow_five_exact_mul_five_below`
- `FloatingPointFormat.problem2_10_ieeeDouble_three_mul_two_pow_minus_quarter_ulp_rounds`
- `FloatingPointFormat.problem2_10_ieeeDouble_three_mul_two_pow_fifths_times_five`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_three_mul_two_pow_five`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_three_mul_two_pow_fifths_mul_five_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_three_mul_two_pow_five_exact_mul_five_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_three_mul_two_pow_minus_quarter_ulp_rounds`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_three_mul_two_pow_fifths_times_five`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_three_mul_two_pow_fifths_times_five`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_five_finiteNormalRange`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_fifths_rounds_to_upper`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_five`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_fifths_mul_five_above_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_five_exact_mul_five_above_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_plus_quarter_ulp_rounds_to_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_fifths_times_five`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_five`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_fifths_mul_five_below_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_five_exact_mul_five_below_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_two_pow_plus_quarter_ulp_rounds_to_neg_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_fifths_times_five`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_fifths_times_five`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_nine_finiteNormalRange`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_ninths_rounds_to_lower`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_nine`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_ninths_mul_nine_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_nine_exact_mul_nine_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_ninths_times_nine`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_nine`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_ninths_mul_nine_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_nine_exact_mul_nine_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_ninths_times_nine`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_ninths_times_nine`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_minus_one_sixteenth_ulp_rounds_to_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_seventeen_finiteNormalRange`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_seventeenths_rounds_to_lower`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_seventeen`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_seventeenths_mul_seventeen_below`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_seventeen_exact_mul_seventeen_below`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_seventeenths_times_seventeen`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_seventeen`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_seventeenths_mul_seventeen_below`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_seventeen_exact_mul_seventeen_below`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_two_pow_minus_one_sixteenth_ulp_rounds_to_neg_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_seventeenths_times_seventeen`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_seventeenths_times_seventeen`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_plus_one_eighth_ulp_rounds_to_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_thirtythree_finiteNormalRange`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_thirtythirds_rounds_to_upper`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_thirtythree`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_thirtythirds_mul_thirtythree_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_thirtythree_exact_mul_thirtythree_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_thirtythirds_times_thirtythree`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_thirtythree`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_thirtythirds_mul_thirtythree_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_thirtythree_exact_mul_thirtythree_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_two_pow_plus_one_eighth_ulp_rounds_to_neg_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_thirtythirds_times_thirtythree`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_thirtythirds_times_thirtythree`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_sixtyfive_finiteNormalRange`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_sixtyfifths_rounds_to_upper`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_sixtyfive`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_sixtyfifths_mul_sixtyfive_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_sixtyfive_exact_mul_sixtyfive_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_sixtyfifths_times_sixtyfive`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_sixtyfive`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_sixtyfifths_mul_sixtyfive_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_sixtyfive_exact_mul_sixtyfive_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_sixtyfifths_times_sixtyfive`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_sixtyfifths_times_sixtyfive`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_onehundredtwentynine_finiteNormalRange`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_onehundredtwentyninths_rounds_to_lower`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_onehundredtwentynine`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_onehundredtwentyninths_mul_onehundredtwentynine_below`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_onehundredtwentynine_exact_mul_onehundredtwentynine_below`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_onehundredtwentyninths_times_onehundredtwentynine`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_onehundredtwentynine`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_onehundredtwentyninths_mul_onehundredtwentynine_below`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_onehundredtwentynine_exact_mul_onehundredtwentynine_below`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_onehundredtwentyninths_times_onehundredtwentynine`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_onehundredtwentyninths_times_onehundredtwentynine`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_plus_one_sixteenth_ulp_rounds_to_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_twohundredfiftyseven_finiteNormalRange`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_twohundredfiftysevenths_rounds_to_upper`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_twohundredfiftyseven`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_twohundredfiftysevenths_mul_twohundredfiftyseven_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_twohundredfiftyseven_exact_mul_twohundredfiftyseven_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_twohundredfiftysevenths_times_twohundredfiftyseven`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_twohundredfiftyseven`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_twohundredfiftysevenths_mul_twohundredfiftyseven_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_twohundredfiftyseven_exact_mul_twohundredfiftyseven_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_two_pow_plus_one_sixteenth_ulp_rounds_to_neg_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_twohundredfiftysevenths_times_twohundredfiftyseven`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_twohundredfiftysevenths_times_twohundredfiftyseven`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_fivehundredthirteen_finiteNormalRange`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_fivehundredthirteenths_rounds_to_lower`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_fivehundredthirteen`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_fivehundredthirteenths_mul_fivehundredthirteen_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_fivehundredthirteen_exact_mul_fivehundredthirteen_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_fivehundredthirteenths_times_fivehundredthirteen`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_fivehundredthirteen`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_fivehundredthirteenths_mul_fivehundredthirteen_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_fivehundredthirteen_exact_mul_fivehundredthirteen_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_fivehundredthirteenths_times_fivehundredthirteen`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_fivehundredthirteenths_times_fivehundredthirteen`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_minus_one_twohundredfiftysixth_ulp_rounds_to_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_two_pow_minus_one_twohundredfiftysixth_ulp_rounds_to_neg_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_onethousandtwentyfive_finiteNormalRange`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_onethousandtwentyfifths_rounds_to_lower`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_onethousandtwentyfive`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_onethousandtwentyfifths_mul_onethousandtwentyfive_below`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_onethousandtwentyfive_exact_mul_onethousandtwentyfive_below`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_onethousandtwentyfifths_times_onethousandtwentyfive`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_onethousandtwentyfive`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_onethousandtwentyfifths_mul_onethousandtwentyfive_below`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_onethousandtwentyfive_exact_mul_onethousandtwentyfive_below`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_onethousandtwentyfifths_times_onethousandtwentyfive`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_onethousandtwentyfifths_times_onethousandtwentyfive`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_twothousandfortynine_finiteNormalRange`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_twothousandfortyninths_rounds_to_upper`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_twothousandfortynine`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_twothousandfortyninths_mul_twothousandfortynine_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_twothousandfortynine_exact_mul_twothousandfortynine_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_twothousandfortyninths_times_twothousandfortynine`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_twothousandfortynine`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_twothousandfortyninths_mul_twothousandfortynine_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_twothousandfortynine_exact_mul_twothousandfortynine_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_twothousandfortyninths_times_twothousandfortynine`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_twothousandfortyninths_times_twothousandfortynine`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_plus_one_twohundredfiftysixth_ulp_rounds_to_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_two_pow_plus_one_twohundredfiftysixth_ulp_rounds_to_neg_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_fourthousandninetyseven_finiteNormalRange`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_fourthousandninetysevenths_rounds_to_upper`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_fourthousandninetyseven`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_fourthousandninetysevenths_mul_fourthousandninetyseven_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_fourthousandninetyseven_exact_mul_fourthousandninetyseven_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_fourthousandninetysevenths_times_fourthousandninetyseven`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_fourthousandninetyseven`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_fourthousandninetysevenths_mul_fourthousandninetyseven_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_fourthousandninetyseven_exact_mul_fourthousandninetyseven_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_fourthousandninetysevenths_times_fourthousandninetyseven`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_fourthousandninetysevenths_times_fourthousandninetyseven`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_plus_one_eightthousandonehundredninetysecond_ulp_rounds_to_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_two_pow_plus_one_eightthousandonehundredninetysecond_ulp_rounds_to_neg_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_eightthousandonehundredninetythree_finiteNormalRange`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_eightthousandonehundredninetythirds_rounds_to_upper`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_eightthousandonehundredninetythree`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_eightthousandonehundredninetythirds_mul_eightthousandonehundredninetythree_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_eightthousandonehundredninetythree_exact_mul_eightthousandonehundredninetythree_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_eightthousandonehundredninetythirds_times_eightthousandonehundredninetythree`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_eightthousandonehundredninetythree`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_eightthousandonehundredninetythirds_mul_eightthousandonehundredninetythree_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_eightthousandonehundredninetythree_exact_mul_eightthousandonehundredninetythree_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_eightthousandonehundredninetythirds_times_eightthousandonehundredninetythree`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_eightthousandonehundredninetythirds_times_eightthousandonehundredninetythree`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_sixteenthousandthreehundredeightyfive_finiteNormalRange`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_sixteenthousandthreehundredeightyfifths_rounds_to_lower`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_sixteenthousandthreehundredeightyfive`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_sixteenthousandthreehundredeightyfifths_mul_sixteenthousandthreehundredeightyfive_below`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_sixteenthousandthreehundredeightyfive_exact_mul_sixteenthousandthreehundredeightyfive_below`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_sixteenthousandthreehundredeightyfifths_times_sixteenthousandthreehundredeightyfive`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_sixteenthousandthreehundredeightyfive`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_sixteenthousandthreehundredeightyfifths_mul_sixteenthousandthreehundredeightyfive_below`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_sixteenthousandthreehundredeightyfive_exact_mul_sixteenthousandthreehundredeightyfive_below`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_sixteenthousandthreehundredeightyfifths_times_sixteenthousandthreehundredeightyfive`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_sixteenthousandthreehundredeightyfifths_times_sixteenthousandthreehundredeightyfive`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_thirtytwothousandsevenhundredsixtynine_finiteNormalRange`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_thirtytwothousandsevenhundredsixtyninths_rounds_to_lower`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_thirtytwothousandsevenhundredsixtynine`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_thirtytwothousandsevenhundredsixtyninths_mul_thirtytwothousandsevenhundredsixtynine_below`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_thirtytwothousandsevenhundredsixtynine_exact_mul_thirtytwothousandsevenhundredsixtynine_below`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_thirtytwothousandsevenhundredsixtyninths_times_thirtytwothousandsevenhundredsixtynine`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_thirtytwothousandsevenhundredsixtynine`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_thirtytwothousandsevenhundredsixtyninths_mul_thirtytwothousandsevenhundredsixtynine_below`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_thirtytwothousandsevenhundredsixtynine_exact_mul_thirtytwothousandsevenhundredsixtynine_below`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_thirtytwothousandsevenhundredsixtyninths_times_thirtytwothousandsevenhundredsixtynine`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_thirtytwothousandsevenhundredsixtyninths_times_thirtytwothousandsevenhundredsixtynine`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_minus_one_fourthousandninetysixth_ulp_rounds_to_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_two_pow_minus_one_fourthousandninetysixth_ulp_rounds_to_neg_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_sixtyfivethousandfivehundredthirtyseven_finiteNormalRange`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_sixtyfivethousandfivehundredthirtysevenths_rounds_to_lower`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_sixtyfivethousandfivehundredthirtyseven`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_sixtyfivethousandfivehundredthirtysevenths_mul_sixtyfivethousandfivehundredthirtyseven_below`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_sixtyfivethousandfivehundredthirtyseven_exact_mul_sixtyfivethousandfivehundredthirtyseven_below`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_sixtyfivethousandfivehundredthirtysevenths_times_sixtyfivethousandfivehundredthirtyseven`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_sixtyfivethousandfivehundredthirtyseven`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_sixtyfivethousandfivehundredthirtysevenths_mul_sixtyfivethousandfivehundredthirtyseven_below`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_sixtyfivethousandfivehundredthirtyseven_exact_mul_sixtyfivethousandfivehundredthirtyseven_below`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_sixtyfivethousandfivehundredthirtysevenths_times_sixtyfivethousandfivehundredthirtyseven`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_sixtyfivethousandfivehundredthirtysevenths_times_sixtyfivethousandfivehundredthirtyseven`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_minus_one_sixtythreethousandfivehundredthirtysixth_ulp_rounds_to_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_two_pow_minus_one_sixtythreethousandfivehundredthirtysixth_ulp_rounds_to_neg_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_onehundredthirtyonethousandseventythree_finiteNormalRange`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_onehundredthirtyonethousandseventythirds_rounds_to_lower`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_onehundredthirtyonethousandseventythree`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_onehundredthirtyonethousandseventythirds_mul_onehundredthirtyonethousandseventythree_below`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_onehundredthirtyonethousandseventythree_exact_mul_onehundredthirtyonethousandseventythree_below`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_onehundredthirtyonethousandseventythirds_times_onehundredthirtyonethousandseventythree`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_onehundredthirtyonethousandseventythree`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_onehundredthirtyonethousandseventythirds_mul_onehundredthirtyonethousandseventythree_below`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_onehundredthirtyonethousandseventythree_exact_mul_onehundredthirtyonethousandseventythree_below`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_onehundredthirtyonethousandseventythirds_times_onehundredthirtyonethousandseventythree`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_onehundredthirtyonethousandseventythirds_times_onehundredthirtyonethousandseventythree`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_twohundredsixtytwothousandonehundredfortyfive_finiteNormalRange`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_twohundredsixtytwothousandonehundredfortyfifths_rounds_to_upper`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_twohundredsixtytwothousandonehundredfortyfive`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_twohundredsixtytwothousandonehundredfortyfifths_mul_twohundredsixtytwothousandonehundredfortyfive_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_twohundredsixtytwothousandonehundredfortyfive_exact_mul_twohundredsixtytwothousandonehundredfortyfive_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_twohundredsixtytwothousandonehundredfortyfifths_times_twohundredsixtytwothousandonehundredfortyfive`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_twohundredsixtytwothousandonehundredfortyfive`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_twohundredsixtytwothousandonehundredfortyfifths_mul_twohundredsixtytwothousandonehundredfortyfive_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_twohundredsixtytwothousandonehundredfortyfive_exact_mul_twohundredsixtytwothousandonehundredfortyfive_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_twohundredsixtytwothousandonehundredfortyfifths_times_twohundredsixtytwothousandonehundredfortyfive`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_twohundredsixtytwothousandonehundredfortyfifths_times_twohundredsixtytwothousandonehundredfortyfive`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_plus_one_thirtysecond_ulp_rounds_to_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_two_pow_plus_one_thirtysecond_ulp_rounds_to_neg_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_plus_one_sixtyfourth_ulp_rounds_to_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_two_pow_plus_one_sixtyfourth_ulp_rounds_to_neg_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_plus_one_onehundredtwentyeighth_ulp_rounds_to_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_two_pow_plus_one_onehundredtwentyeighth_ulp_rounds_to_neg_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_plus_one_fivehundredtwelfth_ulp_rounds_to_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_two_pow_plus_one_fivehundredtwelfth_ulp_rounds_to_neg_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_plus_one_onethousandtwentyfourth_ulp_rounds_to_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_two_pow_plus_one_onethousandtwentyfourth_ulp_rounds_to_neg_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_fivehundredtwentyfourthousandtwohundredeightynine_finiteNormalRange`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_fivehundredtwentyfourthousandtwohundredeightyninths_rounds_to_upper`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_fivehundredtwentyfourthousandtwohundredeightynine`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_fivehundredtwentyfourthousandtwohundredeightyninths_mul_fivehundredtwentyfourthousandtwohundredeightynine_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_fivehundredtwentyfourthousandtwohundredeightynine_exact_mul_fivehundredtwentyfourthousandtwohundredeightynine_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_fivehundredtwentyfourthousandtwohundredeightyninths_times_fivehundredtwentyfourthousandtwohundredeightynine`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_fivehundredtwentyfourthousandtwohundredeightynine`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_fivehundredtwentyfourthousandtwohundredeightyninths_mul_fivehundredtwentyfourthousandtwohundredeightynine_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_fivehundredtwentyfourthousandtwohundredeightynine_exact_mul_fivehundredtwentyfourthousandtwohundredeightynine_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_fivehundredtwentyfourthousandtwohundredeightyninths_times_fivehundredtwentyfourthousandtwohundredeightynine`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_fivehundredtwentyfourthousandtwohundredeightyninths_times_fivehundredtwentyfourthousandtwohundredeightynine`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_onemillionfortyeightthousandfivehundredseventyseven_finiteNormalRange`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_onemillionfortyeightthousandfivehundredseventysevenths_rounds_to_upper`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_onemillionfortyeightthousandfivehundredseventyseven`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_onemillionfortyeightthousandfivehundredseventysevenths_mul_onemillionfortyeightthousandfivehundredseventyseven_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_onemillionfortyeightthousandfivehundredseventyseven_exact_mul_onemillionfortyeightthousandfivehundredseventyseven_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_onemillionfortyeightthousandfivehundredseventysevenths_times_onemillionfortyeightthousandfivehundredseventyseven`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_onemillionfortyeightthousandfivehundredseventyseven`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_onemillionfortyeightthousandfivehundredseventysevenths_mul_onemillionfortyeightthousandfivehundredseventyseven_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_onemillionfortyeightthousandfivehundredseventyseven_exact_mul_onemillionfortyeightthousandfivehundredseventyseven_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_onemillionfortyeightthousandfivehundredseventysevenths_times_onemillionfortyeightthousandfivehundredseventyseven`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_onemillionfortyeightthousandfivehundredseventysevenths_times_onemillionfortyeightthousandfivehundredseventyseven`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_plus_one_twothousandfortyeighth_ulp_rounds_to_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_two_pow_plus_one_twothousandfortyeighth_ulp_rounds_to_neg_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_plus_one_fourthousandninetysixth_ulp_rounds_to_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_two_pow_plus_one_fourthousandninetysixth_ulp_rounds_to_neg_two_pow`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_twomillionninetyseventhousandonehundredfiftythree_finiteNormalRange`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_twomillionninetyseventhousandonehundredfiftythirds_rounds_to_upper`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_twomillionninetyseventhousandonehundredfiftythree`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_twomillionninetyseventhousandonehundredfiftythirds_mul_twomillionninetyseventhousandonehundredfiftythree_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_twomillionninetyseventhousandonehundredfiftythree_exact_mul_twomillionninetyseventhousandonehundredfiftythree_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_twomillionninetyseventhousandonehundredfiftythirds_times_twomillionninetyseventhousandonehundredfiftythree`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_twomillionninetyseventhousandonehundredfiftythree`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_twomillionninetyseventhousandonehundredfiftythirds_mul_twomillionninetyseventhousandonehundredfiftythree_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_twomillionninetyseventhousandonehundredfiftythree_exact_mul_twomillionninetyseventhousandonehundredfiftythree_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_twomillionninetyseventhousandonehundredfiftythirds_times_twomillionninetyseventhousandonehundredfiftythree`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_twomillionninetyseventhousandonehundredfiftythirds_times_twomillionninetyseventhousandonehundredfiftythree`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_succ_eighteen`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_succ_eighteenths_mul_eighteen_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_succ_eighteen_exact_mul_eighteen_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_succ_eighteenths_times_eighteen`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_succ_eighteen`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_succ_eighteenths_mul_eighteen_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_succ_eighteen_exact_mul_eighteen_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_succ_eighteenths_times_eighteen`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_succ_eighteenths_times_eighteen`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_succ_six`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_succ_sixths_mul_six_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_succ_six_exact_mul_six_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_succ_sixths_times_six`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_succ_six`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_succ_sixths_mul_six_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_succ_six_exact_mul_six_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_succ_sixths_times_six`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_succ_sixths_times_six`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_succ_ten`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_succ_tenths_mul_ten_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_succ_ten_exact_mul_ten_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_succ_tenths_times_ten`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_succ_ten`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_succ_tenths_mul_ten_below`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_succ_ten_exact_mul_ten_below`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_succ_tenths_times_ten`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_succ_tenths_times_ten`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_add_two_twelve`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_add_two_twelfths_mul_twelve_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_add_two_twelve_exact_mul_twelve_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_add_two_twelfths_times_twelve`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_add_two_twelve`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_add_two_twelfths_mul_twelve_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_add_two_twelve_exact_mul_twelve_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_add_two_twelfths_times_twelve`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_add_two_twelfths_times_twelve`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_add_two_twenty`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_add_two_twentieths_mul_twenty_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_add_two_twenty_exact_mul_twenty_above`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_pow_add_two_twentieths_times_twenty`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_add_two_twenty`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_add_two_twentieths_mul_twenty_below`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_add_two_twenty_exact_mul_twenty_below`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_add_two_twentieths_times_twenty`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_add_two_twentieths_times_twenty`
- `FloatingPointFormat.problem2_10_ieeeDouble_oneSixth_rounds_to_lower`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_one_six`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_oneSixth_mul_six_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_one_six_exact_mul_six_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_one_sixth_times_six`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_one_six`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_oneSixth_mul_six_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_one_six_exact_mul_six_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_midpoint_above_one_rounds_to_neg_one`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_one_sixth_times_six`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_one_sixth_times_six`
- `FloatingPointFormat.problem2_10_ieeeDouble_oneTenth_rounds_to_upper`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_one_ten`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_oneTenth_mul_ten_above_one`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_one_ten_exact_mul_ten_above_one`
- `FloatingPointFormat.problem2_10_ieeeDouble_one_tenth_times_ten`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_one_ten`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_oneTenth_mul_ten_below_neg_one`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_one_ten_exact_mul_ten_below_neg_one`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_one_tenth_times_ten`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_one_tenth_times_ten`
- `FloatingPointFormat.problem2_10_displayed_kahan_hypotheses`
- `FloatingPointFormat.problem2_10_displayed_negative_kahan_hypotheses`
- `FloatingPointFormat.problem2_10_displayed_two_kahan_hypotheses`
- `FloatingPointFormat.problem2_10_displayed_negative_two_kahan_hypotheses`
- `FloatingPointFormat.problem2_10_displayed_four_kahan_hypotheses`
- `FloatingPointFormat.problem2_10_displayed_negative_four_kahan_hypotheses`
- `FloatingPointFormat.problem2_10_displayed_eight_kahan_hypotheses`
- `FloatingPointFormat.problem2_10_displayed_negative_eight_kahan_hypotheses`
- `FloatingPointFormat.problem2_10_displayed_sixteen_kahan_hypotheses`
- `FloatingPointFormat.problem2_10_displayed_negative_sixteen_kahan_hypotheses`
- `FloatingPointFormat.problem2_10_displayed_thirtytwo_kahan_hypotheses`
- `FloatingPointFormat.problem2_10_displayed_negative_thirtytwo_kahan_hypotheses`
- `FloatingPointFormat.problem2_10_ieeeDouble_finiteSystem_one`
- `FloatingPointFormat.problem2_10_ieeeDouble_finiteSystem_neg_one`
- `FloatingPointFormat.problem2_10_ieeeDouble_finiteSystem_two`
- `FloatingPointFormat.problem2_10_ieeeDouble_finiteSystem_neg_two`
- `FloatingPointFormat.problem2_10_ieeeDouble_finiteSystem_four`
- `FloatingPointFormat.problem2_10_ieeeDouble_finiteSystem_neg_four`
- `FloatingPointFormat.problem2_10_ieeeDouble_finiteSystem_eight`
- `FloatingPointFormat.problem2_10_ieeeDouble_finiteSystem_neg_eight`
- `FloatingPointFormat.problem2_10_ieeeDouble_finiteSystem_sixteen`
- `FloatingPointFormat.problem2_10_ieeeDouble_finiteSystem_neg_sixteen`
- `FloatingPointFormat.problem2_10_ieeeDouble_finiteSystem_thirtytwo`
- `FloatingPointFormat.problem2_10_ieeeDouble_finiteSystem_neg_thirtytwo`
- `FloatingPointFormat.problem2_10_ieeeDouble_finiteSystem_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_finiteSystem_neg_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_displayed_trace_finite_inputs`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_displayed_trace_finite_inputs`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_displayed_trace_finite_inputs`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_two_displayed_trace_finite_inputs`
- `FloatingPointFormat.problem2_10_ieeeDouble_four_displayed_trace_finite_inputs`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_four_displayed_trace_finite_inputs`
- `FloatingPointFormat.problem2_10_ieeeDouble_eight_displayed_trace_finite_inputs`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_eight_displayed_trace_finite_inputs`
- `FloatingPointFormat.problem2_10_ieeeDouble_sixteen_displayed_trace_finite_inputs`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_sixteen_displayed_trace_finite_inputs`
- `FloatingPointFormat.problem2_10_ieeeDouble_thirtytwo_displayed_trace_finite_inputs`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_thirtytwo_displayed_trace_finite_inputs`
- `FloatingPointFormat.problem2_10_finiteRoundToEven_zero_div_mul`
- `FloatingPointFormat.problem2_10_ieeeDouble_zero_allowable_denominator_times_denominator`
- `FloatingPointFormat.problem2_10_ieeeDouble_oneThird_rounds_to_lower`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_one_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_oneThird_mul_three_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_one_three_exact_mul_three_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_midpoint_below_one_rounds_to_one`
- `FloatingPointFormat.problem2_10_ieeeDouble_one_third_times_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_twoThirds_rounds_to_lower`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_twoThirds_mul_three_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_two_three_exact_mul_three_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_midpoint_below_two_rounds_to_two`
- `FloatingPointFormat.problem2_10_ieeeDouble_two_thirds_times_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_one_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_oneThird_mul_three_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_one_three_exact_mul_three_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_midpoint_above_neg_one_rounds_to_neg_one`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_one_third_times_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_one_third_times_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_twoThirds_mul_three_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_three_exact_mul_three_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_midpoint_above_two_rounds_to_neg_two`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_two_thirds_times_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_two_thirds_times_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_fourThirds_rounds_to_lower`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_four_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_fourThirds_mul_three_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_four_three_exact_mul_three_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_midpoint_below_four_rounds_to_four`
- `FloatingPointFormat.problem2_10_ieeeDouble_four_thirds_times_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_four_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_fourThirds_mul_three_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_four_three_exact_mul_three_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_midpoint_above_four_rounds_to_neg_four`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_four_thirds_times_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_four_thirds_times_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_eightThirds_rounds_to_lower`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_eight_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_eightThirds_mul_three_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_eight_three_exact_mul_three_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_midpoint_below_eight_rounds_to_eight`
- `FloatingPointFormat.problem2_10_ieeeDouble_eight_thirds_times_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_eight_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_eightThirds_mul_three_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_eight_three_exact_mul_three_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_midpoint_above_eight_rounds_to_neg_eight`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_eight_thirds_times_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_eight_thirds_times_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_sixteenThirds_rounds_to_lower`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_sixteen_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_sixteenThirds_mul_three_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_sixteen_three_exact_mul_three_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_midpoint_below_sixteen_rounds_to_sixteen`
- `FloatingPointFormat.problem2_10_ieeeDouble_sixteen_thirds_times_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_sixteen_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_sixteenThirds_mul_three_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_sixteen_three_exact_mul_three_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_midpoint_above_sixteen_rounds_to_neg_sixteen`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_sixteen_thirds_times_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_sixteen_thirds_times_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_thirtytwoThirds_rounds_to_lower`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_thirtytwo_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_rounded_thirtytwoThirds_mul_three_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_thirtytwo_three_exact_mul_three_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_midpoint_below_thirtytwo_rounds_to_thirtytwo`
- `FloatingPointFormat.problem2_10_ieeeDouble_thirtytwo_thirds_times_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_thirtytwo_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_thirtytwoThirds_mul_three_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_div_neg_thirtytwo_three_exact_mul_three_midpoint`
- `FloatingPointFormat.problem2_10_ieeeDouble_negative_midpoint_above_thirtytwo_rounds_to_neg_thirtytwo`
- `FloatingPointFormat.problem2_10_ieeeDouble_neg_thirtytwo_thirds_times_three`
- `FloatingPointFormat.problem2_10_ieeeDouble_signed_thirtytwo_thirds_times_three`
- `problem2_11EmpiricalSource`
- `problem2_11EmpiricalSource_exhaustive`
- `problem2_11_decimalLeadingDigit`
- `problem2_11_decimalLeadingDigit_digit_between`
- `problem2_11_decimalLeadingDigit_abs_pos`
- `problem2_11_decimalLeadingDigit_normalized_bin`
- `problem2_11_decimalLeadingDigit_exists_scaled_mem_one_ten`
- `problem2_11_powerSample`
- `problem2_11_powerSample_card`
- `problem2_11_powerSample_index_le_1000`
- `problem2_11_powerSample_first`
- `problem2_11_powerSample_last`
- `problem2_11_powerSample_two_last`
- `problem2_11_powerSample_three_last`
- `problem2_11_powerSample_two_pos`
- `problem2_11_powerSample_three_pos`
- `problem2_11_factorialSample`
- `problem2_11_factorialSample_card`
- `problem2_11_factorialSample_index_between`
- `problem2_11_factorialSample_first`
- `problem2_11_factorialSample_last`
- `problem2_11_factorialSample_pos`
- `problem2_11_digitCount`
- `problem2_11_digitFrequency`
- `problem2_11_digitCount_le_sampleSize`
- `problem2_11_digitFrequency_nonneg`
- `problem2_11_digitFrequency_le_one`
- `problem2_11_sum_digitCount_eq_sampleSize`
- `problem2_11_sum_digitFrequency_eq_one`
- `problem2_11_empiricalDigitProbability`
- `problem2_11_empiricalDigitProbability_prob_eq_frequency`
- `problem2_11_empiricalDigitProbability_prob_le_one`
- `FloatingPointFormat.problem2_12_ieeeDouble_predecessor_normalized`
- `FloatingPointFormat.problem2_12_ieeeDouble_one_normalized`
- `FloatingPointFormat.problem2_12_ieeeDouble_rounds_predecessor_to_self`
- `FloatingPointFormat.problem2_12_ieeeDouble_rounds_one_to_self`
- `FloatingPointFormat.problem2_12_ieeeDouble_upper_midpoint_rounds_to_one`
- `FloatingPointFormat.problem2_12_ieeeDouble_rounds_to_predecessor_of_mem_lower_half_cell`
- `FloatingPointFormat.problem2_12_ieeeDouble_rounds_to_one_of_mem_lower_middle_half_cell`
- `FloatingPointFormat.problem2_12_ieeeDouble_rounds_to_one_of_mem_upper_half_cell`
- `FloatingPointFormat.problem2_12_ieeeDouble_final_rounding_options_of_mem_window`
- `FloatingPointFormat.problem2_12_ieeeDouble_reciprocal_finiteNormalRange_of_one_lt_x_lt_two`
- `FloatingPointFormat.problem2_12_ieeeDouble_reciprocal_product_mem_window_of_one_lt_x_lt_two`
- `FloatingPointFormat.problem2_12_ieeeDouble_reciprocal_product_rounding_options`
- `FloatingPointFormat.problem2_13_candidateJ`
- `FloatingPointFormat.problem2_13_candidateX`
- `FloatingPointFormat.problem2_13_predecessorJ`
- `FloatingPointFormat.problem2_13_predecessorX`
- `FloatingPointFormat.problem2_13_sourceX`
- `FloatingPointFormat.problem2_13_sourceProduct`
- `FloatingPointFormat.problem2_13_reciprocalCellQuotient`
- `FloatingPointFormat.problem2_13_quadraticRemainderQuotient`
- `FloatingPointFormat.problem2_13_reciprocalCellQuotient_remainder_ne_zero_of_pos_lt_candidateJ`
- `FloatingPointFormat.problem2_13_reciprocalCellQuotient_remainder_not_half_of_pos_lt_candidateJ`
- `FloatingPointFormat.problem2_13_reciprocalCellQuotient_remainder_half_trichotomy_of_pos_lt_candidateJ`
- `FloatingPointFormat.problem2_13_quadraticRemainderQuotient_le_29_of_lt_candidateJ`
- `FloatingPointFormat.problem2_13_reciprocalCellQuotient_remainder_eq_quadratic_remainder_of_lt_candidateJ`
- `FloatingPointFormat.problem2_13_reciprocalCellQuotient_remainder_le_threshold_of_quadraticQuotient_eq_29`
- `FloatingPointFormat.problem2_13_reciprocalCellQuotient_remainder_le_threshold_of_quadraticQuotient_le_28_of_left`
- `FloatingPointFormat.problem2_13_reciprocalCellQuotient_normalizedMantissas_of_pos_lt_candidateJ`
- `FloatingPointFormat.problem2_13_sourceX_eq_scaled`
- `FloatingPointFormat.problem2_13_sourceX_candidateJ`
- `FloatingPointFormat.problem2_13_sourceX_predecessorJ`
- `FloatingPointFormat.problem2_13_predecessorJ_succ_eq_candidateJ`
- `FloatingPointFormat.problem2_13_candidateX_sub_predecessorX_eq_ulp`
- `FloatingPointFormat.problem2_13_predecessorX_add_ulp_eq_candidateX`
- `FloatingPointFormat.problem2_13_sourceX_le_sourceX`
- `FloatingPointFormat.problem2_13_sourceX_le_predecessorX_of_lt_candidateJ`
- `FloatingPointFormat.problem2_13_sourceX_lt_candidateX_of_lt_candidateJ`
- `FloatingPointFormat.problem2_13_sourceX_finiteSystem_of_lt_two_pow_52`
- `FloatingPointFormat.problem2_13_sourceX_finiteSystem_of_lt_candidateJ`
- `FloatingPointFormat.problem2_13_candidateX_eq_scaled`
- `FloatingPointFormat.problem2_13_candidateX_finiteSystem`
- `FloatingPointFormat.problem2_13_candidateX_between_one_two`
- `FloatingPointFormat.problem2_13_sourceX_between_one_two_of_pos_lt_candidateJ`
- `FloatingPointFormat.problem2_13_sourceX_reciprocal_strict_between_of_scaled_interval`
- `FloatingPointFormat.problem2_13_sourceX_reciprocal_strict_between_of_nat_scaled_interval`
- `FloatingPointFormat.problem2_13_reciprocalCellQuotient_nat_scaled_interval`
- `FloatingPointFormat.problem2_13_sourceX_reciprocal_strict_between_of_quotient_remainder`
- `FloatingPointFormat.problem2_13_reciprocalCellQuotient_midpoint_left_of_twice_remainder_lt`
- `FloatingPointFormat.problem2_13_reciprocalCellQuotient_midpoint_right_of_denominator_lt_twice_remainder`
- `FloatingPointFormat.problem2_13_reciprocalCellQuotient_scaled_product_left_ge_of_remainder_le`
- `FloatingPointFormat.problem2_13_reciprocalCellQuotient_scaled_product_right_ge`
- `FloatingPointFormat.problem2_13_sourceX_reciprocal_left_closer_of_scaled_midpoint`
- `FloatingPointFormat.problem2_13_sourceX_reciprocal_right_closer_of_scaled_midpoint`
- `FloatingPointFormat.problem2_13_sourceX_reciprocal_rounds_to_left_of_adjacent_scaled`
- `FloatingPointFormat.problem2_13_sourceX_reciprocal_rounds_to_right_of_adjacent_scaled`
- `FloatingPointFormat.problem2_13_sourceX_reciprocal_rounds_to_left_of_scaled_interval_midpoint`
- `FloatingPointFormat.problem2_13_sourceX_reciprocal_rounds_to_right_of_scaled_interval_midpoint`
- `FloatingPointFormat.problem2_13_sourceX_reciprocal_rounds_to_left_of_nat_interval_midpoint`
- `FloatingPointFormat.problem2_13_sourceX_reciprocal_rounds_to_right_of_nat_interval_midpoint`
- `FloatingPointFormat.problem2_13_sourceX_reciprocal_rounds_to_left_of_quotient_midpoint`
- `FloatingPointFormat.problem2_13_sourceX_reciprocal_rounds_to_right_of_quotient_midpoint`
- `FloatingPointFormat.problem2_13_sourceX_reciprocal_rounds_to_left_of_quotient_midpoint_of_pos_lt_candidateJ`
- `FloatingPointFormat.problem2_13_sourceX_reciprocal_rounds_to_right_of_quotient_midpoint_of_pos_lt_candidateJ`
- `FloatingPointFormat.problem2_13_sourceX_reciprocal_rounds_to_left_of_quotient_remainder_lt_half`
- `FloatingPointFormat.problem2_13_sourceX_reciprocal_rounds_to_right_of_quotient_remainder_gt_half`
- `FloatingPointFormat.problem2_13_sourceX_rounding_options_of_pos_lt_candidateJ`
- `FloatingPointFormat.problem2_13_sourceProduct_mem_window_of_pos_lt_candidateJ`
- `FloatingPointFormat.problem2_13_sourceProduct_eq_scaled_of_reciprocal_rounds`
- `FloatingPointFormat.problem2_13_sourceProduct_lower_midpoint_le_of_scaled_product_ge`
- `FloatingPointFormat.problem2_13_sourceProduct_lt_lower_midpoint_of_scaled_product_lt`
- `FloatingPointFormat.problem2_13_sourceX_rounds_to_predecessor_of_sourceProduct_lt_lower_midpoint`
- `FloatingPointFormat.problem2_13_sourceX_rounds_to_one_of_lower_midpoint_le`
- `FloatingPointFormat.problem2_13_sourceX_rounds_to_one_iff_lower_midpoint_le`
- `FloatingPointFormat.problem2_13_sourceX_rounds_to_one_of_reciprocal_scaled_product_ge`
- `FloatingPointFormat.problem2_13_sourceX_rounds_to_predecessor_of_reciprocal_scaled_product_lt`
- `FloatingPointFormat.problem2_13_sourceX_rounds_to_one_iff_reciprocal_scaled_product_ge`
- `FloatingPointFormat.problem2_13_sourceX_rounds_to_one_of_left_reciprocal_nat_certificate`
- `FloatingPointFormat.problem2_13_sourceX_rounds_to_one_of_right_reciprocal_nat_certificate`
- `FloatingPointFormat.problem2_13_sourceX_rounds_to_predecessor_of_left_reciprocal_nat_certificate`
- `FloatingPointFormat.problem2_13_sourceX_rounds_to_predecessor_of_right_reciprocal_nat_certificate`
- `FloatingPointFormat.problem2_13_sourceX_rounds_to_one_of_left_reciprocal_quotient_certificate`
- `FloatingPointFormat.problem2_13_sourceX_rounds_to_one_of_right_reciprocal_quotient_certificate`
- `FloatingPointFormat.problem2_13_sourceX_rounds_to_one_of_left_reciprocal_quotient_integer_certificate`
- `FloatingPointFormat.problem2_13_sourceX_rounds_to_one_of_right_reciprocal_quotient_integer_certificate`
- `FloatingPointFormat.problem2_13_sourceX_rounds_to_one_of_left_reciprocal_quotient_remainder_certificate`
- `FloatingPointFormat.problem2_13_sourceX_rounds_to_one_of_right_reciprocal_quotient_remainder_certificate`
- `FloatingPointFormat.problem2_13_sourceX_rounds_to_one_of_left_reciprocal_quotient_remainder_le_threshold`
- `FloatingPointFormat.problem2_13_sourceX_rounds_to_one_of_left_reciprocal_quotient_remainder_lt_half_le_threshold`
- `FloatingPointFormat.problem2_13_sourceX_rounds_to_one_of_left_reciprocal_quadraticQuotient_eq_29`
- `FloatingPointFormat.problem2_13_sourceX_rounds_to_one_of_left_reciprocal_quadraticQuotient_le_28`
- `FloatingPointFormat.problem2_13_sourceX_rounds_to_one_of_right_reciprocal_quotient_remainder_gt_half`
- `FloatingPointFormat.problem2_13_sourceX_rounds_to_one_of_quadraticQuotient_eq_29`
- `FloatingPointFormat.problem2_13_sourceX_rounds_to_one_of_quadraticQuotient_le_28`
- `FloatingPointFormat.problem2_13_sourceX_rounds_to_one_of_pos_lt_candidateJ`
- `FloatingPointFormat.problem2_13_predecessorX_eq_scaled`
- `FloatingPointFormat.problem2_13_predecessorX_finiteSystem`
- `FloatingPointFormat.problem2_13_predecessorX_between_one_two`
- `FloatingPointFormat.problem2_13_predecessor_candidate_adjacentNormalized`
- `FloatingPointFormat.problem2_13_predecessorX_lt_candidateX`
- `FloatingPointFormat.problem2_13_candidate_reciprocal_rounds_to_lower`
- `FloatingPointFormat.problem2_13_candidate_reciprocal_product_eq`
- `FloatingPointFormat.problem2_13_sourceProduct_candidateJ`
- `FloatingPointFormat.problem2_13_sourceProduct_candidateJ_mem_window`
- `FloatingPointFormat.problem2_13_candidate_sourceProduct_lt_lower_midpoint`
- `FloatingPointFormat.problem2_13_candidate_scaled_product_lt_lower_midpoint_threshold`
- `FloatingPointFormat.problem2_13_candidate_rounds_to_predecessor_of_sourceProduct_lower_midpoint`
- `FloatingPointFormat.problem2_13_candidate_rounds_to_predecessor`
- `FloatingPointFormat.problem2_13_candidate_rounds_ne_one`
- `FloatingPointFormat.problem2_13_predecessor_reciprocal_rounds_to_lower`
- `FloatingPointFormat.problem2_13_predecessor_scaled_product_ge_lower_midpoint_threshold`
- `FloatingPointFormat.problem2_13_predecessor_reciprocal_product_eq`
- `FloatingPointFormat.problem2_13_sourceProduct_predecessorJ`
- `FloatingPointFormat.problem2_13_predecessor_sourceProduct_lower_midpoint_le`
- `FloatingPointFormat.problem2_13_predecessor_rounds_to_one_of_sourceProduct_lower_midpoint`
- `FloatingPointFormat.problem2_13_predecessor_rounds_to_one_of_scaled_product_certificate`
- `FloatingPointFormat.problem2_13_predecessor_rounds_to_one`
- `FloatingPointFormat.problem2_14_ieeeDouble_four_thirds_rounds_to_lower`
- `FloatingPointFormat.problem2_14_ieeeDouble_four_thirds_minus_one`
- `FloatingPointFormat.problem2_14_ieeeDouble_three_mul_four_thirds_minus_one`
- `FloatingPointFormat.problem2_14_ieeeDouble_kahan_probe_error`
- `FloatingPointFormat.problem2_14_ieeeDoubleKahanEstimate`
- `FloatingPointFormat.problem2_14_ieeeDoubleKahanEstimate_eq_machineEpsilon`
- `FloatingPointFormat.problem2_14_ieeeDoubleKahanEstimate_eq_two_unitRoundoff`
- `FloatingPointFormat.problem2_14_ieeeSingle_four_thirds_rounds_to_upper`
- `FloatingPointFormat.problem2_14_ieeeSingle_four_thirds_minus_one`
- `FloatingPointFormat.problem2_14_ieeeSingle_three_mul_four_thirds_minus_one`
- `FloatingPointFormat.problem2_14_ieeeSingle_kahan_probe_error`
- `FloatingPointFormat.problem2_14_ieeeSingleKahanEstimate`
- `FloatingPointFormat.problem2_14_ieeeSingleKahanEstimate_eq_machineEpsilon`
- `FloatingPointFormat.problem2_14_ieeeSingleKahanEstimate_eq_two_unitRoundoff`
- `problem2_15_16Probe`
- `problem2_15_16ProbeList`
- `problem2_15_16ProbeList_length`
- `problem2_15_16ProbeList_nodup`
- `problem2_15_16Probe_mem_sourceList`
- `problem2_15_16Environment`
- `problem2_15_16ReferenceResult`
- `problem2_15_16ReferenceEnvironment`
- `problem2_15_16ReferenceEnvironment_eval`
- `problem2_15_reference_zero_pow_zero`
- `problem2_15_16_probe_can_return`
- `problem2_15_16_probe_not_forced_by_core_ieee_model`
- `problem2_16_reference_one_pow_posInf`
- `problem2_16_reference_two_pow_posInf`
- `problem2_16_reference_exp_posInf`
- `problem2_16_reference_exp_negInf`
- `problem2_16_reference_sign_nan`
- `problem2_16_reference_sign_neg_nan`
- `problem2_16_reference_nan_pow_zero`
- `problem2_16_reference_posInf_pow_zero`
- `problem2_16_reference_one_pow_nan`
- `problem2_16_reference_log_posInf`
- `problem2_16_reference_log_negInf`
- `problem2_16_reference_log_posZero`
- `problem2_17_discriminant`
- `problem2_17_computedDiscriminant`
- `problem2_17_true_discriminant_nonnegative`
- `problem2_17_true_discriminant_eq_one_tenth`
- `problem2_17_computed_discriminant_negative`
- `problem2_17_standard_model_witness_exact_values`
- `problem2_17_standard_model_counterexample`
- `FloatingPointFormat.problem2_17_decimalOneDigitThreeExponentFormat_finiteSystem_nine_tenths`
- `problem2_17_standard_model_counterexample_with_decimal_finite_inputs`
- `ieeeNaiveMax`
- `ieeeNaiveMax_eq_left_of_ieeeGt`
- `ieeeNaiveMax_eq_right_of_not_ieeeGt`
- `ieeeNaiveMax_finite_finite_left_of_lt`
- `ieeeNaiveMax_finite_finite_right_of_le`
- `ieeeNaiveMax_finite_finite_eq_max`
- `ieeeNaiveMax_left_nan`
- `ieeeNaiveMax_right_nan`
- `ieeeNaiveMax_nan_finite`
- `ieeeNaiveMax_finite_nan`
- `ieeeNaiveMax_nan_finite_ne_finite_nan`
- `ieeeNaiveMax_left_nan_finite_result_not_nan`
- `ieeeNaiveMax_concrete_nan_counterexample`
- `ieeeNaiveMax_not_nan_propagating`
- `ieeeNaiveMax_finite_correct_but_not_nan_propagating`
- `problem2_22_guard_digit_a_sub_b_exact`
- `problem2_22_kahanHeronArea_relError_le_gamma9_unitRoundoff`
- `problem2_23_guardDigitY_eq_x_of_finiteSystem`
- `problem2_23_noGuardY_error_formula`
- `problem2_23_binaryNoGuardScaledMantissa_eq_add_mod_two`
- `problem2_23_binaryNoGuardScaledMantissa_eq_self_of_even`
- `problem2_23_binaryNoGuardScaledMantissa_eq_succ_of_odd`
- `problem2_23_binaryNoGuardYScaled_error_eq_low_bit`
- `problem2_23_binaryNoGuardYScaled_eq_scaledValue_add_low_bit`
- `problem2_23_guard_and_binary_noGuard_summary`
- `FloatingPointFormat.problem2_24_eval`
- `FloatingPointFormat.problem2_24_y1`
- `FloatingPointFormat.problem2_24_y2`
- `FloatingPointFormat.problem2_24_y3`
- `FloatingPointFormat.problem2_24_exactExpr`
- `FloatingPointFormat.problem2_24_exactExpr_eq_three_mul_sub_one`
- `FloatingPointFormat.problem2_24_exactExpr_eq_zero_iff`
- `FloatingPointFormat.problem2_24_exactExpr_ne_zero_of_ne_one_third`
- `FloatingPointFormat.problem2_24_eval_eq_rounded_last_sum`
- `FloatingPointFormat.problem2_24_eval_eq_last_exact_of_finiteSystem_last_sum`
- `FloatingPointFormat.problem2_24_eval_eq_zero_iff_last_sum_eq_zero_of_finiteSystem_last_sum`
- `FloatingPointFormat.problem2_24_y3_eq_neg_x_of_eval_eq_zero_of_finiteSystem_last_sum`
- `FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_last_sum_of_last_sum_ne_zero`
- `FloatingPointFormat.problem2_24_eval_eq_three_mul_sub_one_of_finiteSystem_intermediates`
- `FloatingPointFormat.problem2_24_eval_eq_exactExpr_of_finiteSystem_intermediates`
- `FloatingPointFormat.problem2_24_eq_one_third_of_eval_eq_zero_of_finiteSystem_intermediates`
- `FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_intermediates_of_ne_one_third`
- `FloatingPointFormat.problem2_24_eval_eq_zero_implies_not_all_finiteSystem_intermediates_of_ne_one_third`
- `FloatingPointFormat.problem2_24_eval_eq_zero_implies_exists_nonfinite_exact_intermediate_of_ne_one_third`
- `FloatingPointFormat.problem2_24_eval_eq_zero_implies_later_nonfinite_exact_intermediate_of_finiteSystem_input_of_ne_one_third`
- `FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_input_of_ne_one_third_of_second_third_exact_intermediates`
- `FloatingPointFormat.problem2_24_eval_eq_zero_implies_second_or_third_nonfinite_exact_intermediate_of_finiteSystem_input_of_ne_one_third`
- `FloatingPointFormat.finiteRoundToEven_eq_zero_abs_le_half_minSubnormalMagnitude_of_subnormalMantissa_one`
- `FloatingPointFormat.finiteSystem_exists_int_mul_minSubnormalMagnitude`
- `FloatingPointFormat.int_mul_minSubnormalMagnitude_abs_ge_of_ne_zero`
- `FloatingPointFormat.finiteSystem_add_eq_zero_of_abs_le_half_minSubnormalMagnitude`
- `FloatingPointFormat.problem2_24_eval_eq_zero_last_sum_abs_le_half_minSubnormalMagnitude`
- `FloatingPointFormat.problem2_24_y1_finiteSystem`
- `FloatingPointFormat.problem2_24_y2_finiteSystem`
- `FloatingPointFormat.problem2_24_y3_finiteSystem`
- `FloatingPointFormat.problem2_24_y1_first_sub_nearestRoundingToFinite`
- `FloatingPointFormat.problem2_24_y1_first_sub_distance_to_x_le_half`
- `FloatingPointFormat.problem2_24_y1_first_sub_distance_to_zero_product_le`
- `FloatingPointFormat.problem2_24_y1_nonneg_of_half_le`
- `FloatingPointFormat.problem2_24_y1_le_two_mul_x_sub_one_of_half_le`
- `FloatingPointFormat.problem2_24_y1_between_zero_and_two_mul_x_sub_one_of_half_le`
- `FloatingPointFormat.problem2_24_y1_nonpos_of_le_half`
- `FloatingPointFormat.problem2_24_two_mul_x_sub_one_le_y1_of_le_half`
- `FloatingPointFormat.problem2_24_y1_between_two_mul_x_sub_one_and_zero_of_le_half`
- `FloatingPointFormat.problem2_24_y1_between_x_sub_one_and_x_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_y2_second_add_nearestRoundingToFinite`
- `FloatingPointFormat.problem2_24_y2_second_add_distance_to_zero_le_self`
- `FloatingPointFormat.problem2_24_y2_second_add_distance_to_zero_product_le`
- `FloatingPointFormat.problem2_24_y2_nonneg_of_y1_add_x_nonneg`
- `FloatingPointFormat.problem2_24_y2_le_two_mul_y1_add_x_of_y1_add_x_nonneg`
- `FloatingPointFormat.problem2_24_y2_between_zero_and_two_mul_y1_add_x_of_y1_add_x_nonneg`
- `FloatingPointFormat.problem2_24_y2_nonpos_of_y1_add_x_nonpos`
- `FloatingPointFormat.problem2_24_two_mul_y1_add_x_le_y2_of_y1_add_x_nonpos`
- `FloatingPointFormat.problem2_24_y2_between_two_mul_y1_add_x_and_zero_of_y1_add_x_nonpos`
- `FloatingPointFormat.problem2_24_y2_second_add_distance_to_y1_le_abs_x`
- `FloatingPointFormat.problem2_24_y2_second_add_distance_to_x_le_abs_y1`
- `FloatingPointFormat.problem2_24_y2_second_add_distance_to_x_product_le_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_eval_eq_zero_last_sum_eq_zero_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_y3_eq_neg_x_of_eval_eq_zero_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_y3_eq_neg_x_last_sub_nearestRoundingToFinite`
- `FloatingPointFormat.problem2_24_y3_eq_neg_x_last_sub_minimal`
- `FloatingPointFormat.problem2_24_y3_eq_neg_x_last_sub_distance_to_y2_le_half`
- `FloatingPointFormat.problem2_24_y3_eq_neg_x_last_sub_distance_to_zero_product_le`
- `FloatingPointFormat.problem2_24_y3_eq_neg_x_last_sub_distance_to_neg_half_product_nonneg`
- `FloatingPointFormat.problem2_24_y3_eq_neg_x_last_sub_y2_bound_of_pos`
- `FloatingPointFormat.problem2_24_y3_eq_neg_x_last_sub_y2_lower_bound_of_lt_half`
- `FloatingPointFormat.problem2_24_eval_eq_zero_last_sub_minimal_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_eval_eq_zero_last_sub_distance_to_y2_le_half_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_eval_eq_zero_last_sub_distance_to_zero_product_le_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_eval_eq_zero_last_sub_y2_bound_of_pos_finiteSystem_input`
- `FloatingPointFormat.problem2_24_eval_eq_zero_last_sub_y2_lower_bound_of_lt_half_finiteSystem_input`
- `FloatingPointFormat.problem2_24_eval_eq_zero_y2_pos_of_lt_half_finiteSystem_input`
- `FloatingPointFormat.problem2_24_eval_eq_zero_y1_add_x_pos_of_lt_half_finiteSystem_input`
- `FloatingPointFormat.problem2_24_eval_eq_zero_y2_add_x_between_zero_and_one_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_eval_eq_zero_input_nonneg_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_eval_eq_zero_input_le_one_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_eval_eq_zero_input_mem_unit_interval_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_input_of_half_le`
- `FloatingPointFormat.problem2_24_eval_zero_ne_zero_of_half_and_one_finiteSystem`
- `FloatingPointFormat.problem2_24_eval_eq_zero_input_pos_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_eval_eq_zero_input_mem_open_lower_half_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_eval_eq_zero_input_mem_tenth_to_half_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_y1_first_sub_distance_to_neg_x_product_nonneg_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_y1_le_three_mul_x_sub_one_of_y1_add_x_pos_finiteSystem_input`
- `FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_input_of_lt_one_six`
- `FloatingPointFormat.problem2_24_eval_eq_zero_input_ge_one_six_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_eval_eq_zero_input_mem_one_six_to_half_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_input_of_lt_nine_thirty_four`
- `FloatingPointFormat.problem2_24_eval_eq_zero_input_ge_nine_thirty_four_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_eval_eq_zero_input_mem_nine_thirty_four_to_half_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_y1_eq_x_sub_half_of_finiteSystem_input_of_quarter_lt_of_lt_one`
- `FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_input_of_lt_five_eighteen`
- `FloatingPointFormat.problem2_24_eval_eq_zero_input_ge_five_eighteen_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_eval_eq_zero_input_mem_five_eighteen_to_half_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_y3_eq_neg_x_last_sub_distance_to_y1_product_nonneg`
- `FloatingPointFormat.problem2_24_y3_eq_neg_x_last_sub_y2_y1_bound_of_y1_add_x_pos`
- `FloatingPointFormat.problem2_24_eval_eq_zero_last_sub_y2_y1_bound_of_lt_half_finiteSystem_input`
- `FloatingPointFormat.problem2_24_eval_eq_zero_y2_le_quarter_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_input_of_five_twelfths_lt`
- `FloatingPointFormat.problem2_24_eval_eq_zero_input_le_five_twelfths_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_eval_eq_zero_input_mem_five_eighteen_to_five_twelfths_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_y2_eq_two_mul_x_sub_half_of_finiteSystem_input_of_quarter_lt_of_lt_one_third`
- `FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_input_of_lt_three_tenths`
- `FloatingPointFormat.problem2_24_eval_eq_zero_input_ge_three_tenths_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_eval_eq_zero_input_mem_three_tenths_to_five_twelfths_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_y3_eq_neg_x_last_sub_distance_to_neg_const_product_le`
- `FloatingPointFormat.problem2_24_eval_eq_zero_last_sub_distance_to_neg_const_product_le_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_input_of_const_gt_one_third_of_lt_two_sub_const_div_five`
- `FloatingPointFormat.problem2_24_eval_eq_zero_input_ge_two_sub_const_div_five_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_input_of_three_eighths_lt`
- `FloatingPointFormat.problem2_24_eval_eq_zero_input_le_three_eighths_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_input_of_lt_fifty_three_one_sixty`
- `FloatingPointFormat.problem2_24_eval_eq_zero_input_ge_fifty_three_one_sixty_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_eval_eq_zero_input_mem_fifty_three_one_sixty_to_three_eighths_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_ieeeSingle_half_finiteSystem`
- `FloatingPointFormat.problem2_24_ieeeDouble_half_finiteSystem`
- `FloatingPointFormat.problem2_24_ieeeSingle_one_finiteSystem`
- `FloatingPointFormat.problem2_24_ieeeDouble_one_finiteSystem`
- `FloatingPointFormat.problem2_24_ieeeSingle_subnormalMantissa_one`
- `FloatingPointFormat.problem2_24_ieeeDouble_subnormalMantissa_one`
- `FloatingPointFormat.problem2_24_ieeeSingle_oneThird_rounds_to_upper`
- `FloatingPointFormat.problem2_24_ieeeSingle_one_third_not_finiteSystem`
- `FloatingPointFormat.problem2_24_ieeeDouble_one_third_not_finiteSystem`
- `FloatingPointFormat.problem2_24_ieeeSingle_finiteSystem_ne_one_third`
- `FloatingPointFormat.problem2_24_ieeeDouble_finiteSystem_ne_one_third`
- `FloatingPointFormat.problem2_24_ieeeSingle_exactExpr_ne_zero_of_finiteSystem`
- `FloatingPointFormat.problem2_24_ieeeDouble_exactExpr_ne_zero_of_finiteSystem`
- `FloatingPointFormat.problem2_24_ieeeSingle_eval_ne_zero_of_finiteSystem_intermediates`
- `FloatingPointFormat.problem2_24_ieeeDouble_eval_ne_zero_of_finiteSystem_intermediates`
- `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_implies_exists_nonfinite_exact_intermediate`
- `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_implies_exists_nonfinite_exact_intermediate`
- `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_implies_later_nonfinite_exact_intermediate`
- `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_implies_later_nonfinite_exact_intermediate`
- `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_implies_second_or_third_nonfinite_exact_intermediate`
- `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_implies_second_or_third_nonfinite_exact_intermediate`
- `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_last_sum_abs_le_half_minSubnormalMagnitude`
- `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_last_sum_abs_le_half_minSubnormalMagnitude`
- `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_last_sum_eq_zero_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_last_sum_eq_zero_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_ieeeSingle_y3_eq_neg_x_of_eval_eq_zero_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_ieeeDouble_y3_eq_neg_x_of_eval_eq_zero_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_implies_y3_eq_neg_x_and_exists_nonfinite_exact_intermediate`
- `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_implies_y3_eq_neg_x_and_exists_nonfinite_exact_intermediate`
- `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_last_sub_distance_to_y2_le_half_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_last_sub_distance_to_y2_le_half_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_last_sub_distance_to_zero_product_le_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_last_sub_distance_to_zero_product_le_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_last_sub_y2_bound_of_pos_finiteSystem_input`
- `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_last_sub_y2_bound_of_pos_finiteSystem_input`
- `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_input_mem_unit_interval_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_input_mem_unit_interval_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_ieeeSingle_eval_ne_zero_of_finiteSystem_input_of_half_le`
- `FloatingPointFormat.problem2_24_ieeeDouble_eval_ne_zero_of_finiteSystem_input_of_half_le`
- `FloatingPointFormat.problem2_24_ieeeSingle_eval_zero_ne_zero`
- `FloatingPointFormat.problem2_24_ieeeDouble_eval_zero_ne_zero`
- `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_input_pos_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_input_pos_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_input_mem_open_lower_half_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_input_mem_open_lower_half_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_input_mem_tenth_to_half_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_input_mem_tenth_to_half_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_input_mem_one_six_to_half_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_input_mem_one_six_to_half_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_input_mem_nine_thirty_four_to_half_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_input_mem_nine_thirty_four_to_half_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_input_mem_five_eighteen_to_half_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_input_mem_five_eighteen_to_half_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_input_mem_five_eighteen_to_five_twelfths_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_input_mem_five_eighteen_to_five_twelfths_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_input_mem_three_tenths_to_five_twelfths_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_input_mem_three_tenths_to_five_twelfths_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_ieeeSingle_three_eighths_finiteSystem`
- `FloatingPointFormat.problem2_24_ieeeDouble_three_eighths_finiteSystem`
- `FloatingPointFormat.problem2_24_ieeeSingle_eleven_thirty_two_finiteSystem`
- `FloatingPointFormat.problem2_24_ieeeDouble_eleven_thirty_two_finiteSystem`
- `FloatingPointFormat.problem2_24_ieeeSingle_one_third_upper_neighbor_finiteSystem`
- `FloatingPointFormat.problem2_24_ieeeDouble_one_third_upper_neighbor_finiteSystem`
- `FloatingPointFormat.problem2_24_ieeeSingle_one_quarter_finiteSystem`
- `FloatingPointFormat.problem2_24_ieeeDouble_one_quarter_finiteSystem`
- `FloatingPointFormat.problem2_24_ieeeSingle_second_exact_intermediate_finiteSystem_of_neg_one_mantissa_mem_upper_branch`
- `FloatingPointFormat.problem2_24_ieeeDouble_second_exact_intermediate_finiteSystem_of_neg_one_mantissa_mem_upper_branch`
- `FloatingPointFormat.problem2_24_ieeeSingle_finiteSystem_upper_branch_exists_neg_one_mantissa`
- `FloatingPointFormat.problem2_24_ieeeDouble_finiteSystem_upper_branch_exists_neg_one_mantissa`
- `FloatingPointFormat.problem2_24_ieeeSingle_second_exact_intermediate_finiteSystem_of_finiteSystem_upper_branch`
- `FloatingPointFormat.problem2_24_ieeeDouble_second_exact_intermediate_finiteSystem_of_finiteSystem_upper_branch`
- `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_finiteSystem_upper_branch`
- `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_finiteSystem_upper_branch`
- `FloatingPointFormat.problem2_24_ieeeSingle_upper_neighbor_le_of_finiteSystem_of_one_third_lt`
- `FloatingPointFormat.problem2_24_ieeeDouble_upper_neighbor_le_of_finiteSystem_of_one_third_lt`
- `FloatingPointFormat.problem2_24_ieeeSingle_upper_neighbor_le_of_finiteSystem_of_one_third_le`
- `FloatingPointFormat.problem2_24_ieeeDouble_upper_neighbor_le_of_finiteSystem_of_one_third_le`
- `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_one_third_le`
- `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_one_third_le`
- `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_implies_third_exact_intermediate_nonfinite`
- `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_implies_third_exact_intermediate_nonfinite`
- `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_input_mem_fifty_three_one_sixty_to_three_eighths_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_input_mem_fifty_three_one_sixty_to_three_eighths_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_input_ge_two_sub_one_third_upper_neighbor_div_five_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_input_ge_two_sub_one_third_upper_neighbor_div_five_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_input_mem_one_third_upper_neighbor_lower_to_three_eighths_of_finiteSystem_input`
- `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_input_mem_one_third_upper_neighbor_lower_to_three_eighths_of_finiteSystem_input`
- `problem2_25_finiteRoundedProduct`
- `problem2_25_finiteFmaDetWithRoundedProduct`
- `problem2_25_roundedProductResidualsRepresentable`
- `problem2_25_finiteRoundedProduct_finiteSystem`
- `problem2_25_fmaCore_eq_det2x2`
- `problem2_25_finiteFmaCorrection_eq_exact_of_finiteSystem`
- `problem2_25_finiteFmaMain_eq_exact_of_finiteSystem`
- `problem2_25_finiteFmaCore_eq_det2x2_of_exact_residuals`
- `problem2_25_finiteFmaDet_signedRelErrorWitness_lt`
- `problem2_25_finiteFmaDet_relError_lt_unitRoundoff`
- `problem2_25_finiteFmaDetWithRoundedProduct_signedRelErrorWitness_lt`
- `problem2_25_finiteFmaDetWithRoundedProduct_relError_lt_unitRoundoff`
- `problem2_25_finiteFmaDetWithRoundedProduct_highRelativeAccuracy`
- `reciprocalNewtonCorrection`
- `reciprocalNewtonStep`
- `reciprocalNewtonStepIter`
- `reciprocalNewtonRoundedStep`
- `reciprocalNewtonRoundedStepErrorEval`
- `reciprocalNewtonRoundedResidual`
- `reciprocalNewtonRoundedResidualErrorEval`
- `reciprocalNewtonRoundedResidualAbsBound`
- `reciprocalNewtonCorrection_eq_step`
- `reciprocalNewtonStep_residual_sq`
- `reciprocalNewtonStep_error_sq`
- `reciprocalNewtonStep_fixed_point`
- `reciprocalNewtonStepIter_residual_pow_two`
- `division_eq_multiply_by_reciprocal`
- `divisionViaReciprocal_error_eq_residual`
- `reciprocalNewtonStep_division_error_sq`
- `reciprocalNewtonStepIter_division_error_pow_two`
- `reciprocalNewtonRoundedResidualErrorEval_zero_errors`
- `reciprocalNewtonRoundedStepErrorEval_residual_eq`
- `reciprocalNewtonRoundedResidualErrorEval_eq_sq_plus_roundoff`
- `reciprocalNewtonRoundedResidualErrorEval_abs_le`
- `reciprocalNewtonRoundedResidualAbsBound_le_radius`
- `reciprocalNewtonRoundedResidualAbsBound_le_small_radius`
- `reciprocalNewtonRoundedResidualErrorEval_abs_le_small_radius`
- `reciprocalNewtonRoundedResidualErrorEval_abs_le_self_radius`
- `reciprocalNewtonRoundedResidualErrorEvalIter`
- `reciprocalNewtonRoundedResidualEnvelope`
- `reciprocalNewtonRoundedResidualEnvelope_nonneg`
- `reciprocalNewtonRoundedResidualEnvelope_le_self_radius`
- `reciprocalNewtonRoundedResidualEnvelope_le_roundoff_floor`
- `reciprocalNewtonRoundedResidualEnvelope_le_geometric_floor`
- `reciprocalNewtonRoundedResidualErrorEvalIter_abs_le_envelope`
- `reciprocalNewtonRoundedResidualErrorEvalIter_abs_le_envelope_of_self_radius`
- `reciprocalNewtonRoundedResidualErrorEvalIter_abs_le_self_radius`
- `reciprocalNewtonRoundedResidualErrorEvalIter_abs_le_roundoff_floor`
- `reciprocalNewtonRoundedResidualErrorEvalIter_abs_le_geometric_floor`
- `reciprocalNewtonRoundedStep_eq_errorEval`
- `reciprocalNewtonRoundedResidual_eq_errorEval`
- `reciprocalNewtonRoundedResidual_eq_residualErrorEval`
- `reciprocalNewtonRoundedResidual_abs_le_small_radius`
- `reciprocalNewtonRoundedResidual_abs_le_self_radius`
- `reciprocalNewtonRoundedStepIter`
- `reciprocalNewtonRoundedStepIter_residual_abs_le_envelope_of_self_radius`
- `reciprocalNewtonRoundedStepIter_residual_abs_le_geometric_floor`
- `reciprocalNewtonRoundedStepIter_residual_abs_le_roundoff_floor`
- `reciprocalNewtonRoundedStepIter_division_error_abs_le_geometric_floor`
- `reciprocalNewtonRoundedStepIter_division_error_abs_le_roundoff_floor`
- `FloatingPointFormat.reciprocalNewtonFiniteStep`
- `FloatingPointFormat.reciprocalNewtonFiniteStepIter`
- `FloatingPointFormat.reciprocalNewtonFiniteStep_eq_step_of_finiteSystem`
- `FloatingPointFormat.reciprocalNewtonFiniteStep_residual_sq_of_finiteSystem`
- `FloatingPointFormat.reciprocalNewtonFiniteStep_error_sq_of_finiteSystem`
- `FloatingPointFormat.reciprocalNewtonFiniteStepIter_residual_sq_of_finiteSystem`
- `FloatingPointFormat.reciprocalNewtonFiniteStepIter_residual_pow_two_of_finiteSystem`
- `FloatingPointFormat.reciprocalNewtonFiniteStepIter_error_pow_two_of_finiteSystem`
- `FloatingPointFormat.reciprocalNewtonFiniteStepIter_division_error_pow_two_of_finiteSystem`
- `problem2_27_residual`
- `problem2_27_fullAccuracy`
- `problem2_27_residual_eq_zero_iff_fullAccuracy`
- `problem2_27_fullAccuracy_iff_eq_div`
- `problem2_27_zero_exact_residual_of_additive_model_normal_branch`
- `problem2_27_zero_exact_residual_or_underflow_bound_of_additive_model`
- `problem2_27_zero_exact_residual_or_strict_underflow_bound_of_strict_model`
- `problem2_27_fullAccuracy_of_zero_residual_normal_branch`
- `problem2_27_fullAccuracy_or_underflow_bound_of_zero_residual_model`
- `FloatingPointFormat.problem2_27_computedProduct`
- `FloatingPointFormat.problem2_27_computedResidual`
- `FloatingPointFormat.problem2_27_convergenceTest`
- `FloatingPointFormat.problem2_27_computedProduct_eq_exact_of_finiteSystem`
- `FloatingPointFormat.problem2_27_computedResidual_eq_exact_of_finiteSystem`
- `FloatingPointFormat.problem2_27_convergenceTest_iff_fullAccuracy_of_exact_residual_path`
- `FloatingPointFormat.problem2_27_convergenceTest_iff_eq_div_of_exact_residual_path`
- `FloatingPointFormat.problem2_27_convergenceTest_fullAccuracy_or_underflow_bound_of_additive_model`
- `FloatingPointFormat.problem2_27_convergenceTest_fullAccuracy_or_strict_underflow_bound_of_strict_model`
- `FloatingPointFormat.problem2_27_convergenceTest_fullAccuracy_of_additive_model_normal_branch`
- `FloatingPointFormat.problem2_27_convergenceTest_of_fullAccuracy_additive_model_normal_branch`
- `FloatingPointFormat.problem2_27_convergenceTest_iff_fullAccuracy_of_additive_model_normal_branch`
- `FloatingPointFormat.problem2_27_convergenceTest_eq_div_of_additive_model_normal_branch`
- `FloatingPointFormat.problem2_27_convergenceTest_iff_eq_div_of_additive_model_normal_branch`
- `FloatingPointFormat.problem2_27_convergenceTest_eq_div_or_underflow_bound_of_additive_model`
- `FloatingPointFormat.problem2_27_convergenceTest_eq_div_or_strict_underflow_bound_of_strict_model`
- `additiveErrorWitness`
- `oneAdditiveErrorTermZero`
- `additiveUnderflowModelWitness`
- `strictAdditiveUnderflowModelWitness`
- `additiveErrorWitness_of_signedRelErrorWitness`
- `additiveUnderflowModelWitness_normal_branch`
- `strictAdditiveUnderflowModelWitness_normal_branch`
- `additiveErrorWitness_underflow_branch`
- `additiveUnderflowModelWitness_underflow_branch_of_absError_le`
- `strictAdditiveUnderflowModelWitness_underflow_branch_of_absError_lt`
- `noGuardAddWitness`
- `noGuardSubWitness`
- `noGuardMulDivWitness`
- `noGuardBasicOpWitness`
- `noGuardAddWitness_alpha_bound`
- `noGuardAddWitness_beta_bound`
- `noGuardAddWitness_value`
- `noGuardAddWitness_error_eq`
- `noGuardSubWitness_alpha_bound`
- `noGuardSubWitness_beta_bound`
- `noGuardSubWitness_value`
- `noGuardSubWitness_error_eq`
- `noGuardMulDivWitness_delta_bound`
- `noGuardMulDivWitness_signedRelErrorWitness`
- `noGuardMulDivWitness_of_signedRelErrorWitness`
- `noGuardMulDivWitness_error_eq`
- `noGuardBasicOpWitness_add_iff`
- `noGuardBasicOpWitness_sub_iff`
- `noGuardBasicOpWitness_mul_iff`
- `noGuardBasicOpWitness_div_iff`
- `noGuardBinaryT3_exact_difference`
- `noGuardBinaryT3_truncated_difference`
- `noGuardBinaryT3_truncated_factor_two`
- `noGuardBinaryT3_truncated_relError_eq_one`
- `NoGuardFPModel`
- `NoGuardFPModel.round`
- `NoGuardFPModel.u_pos`
- `NoGuardFPModel.model_basicOp`
- `NoGuardFPModel.exactWithUnitRoundoff`
- `NoGuardFPModel.model_add_error_eq`
- `NoGuardFPModel.model_sub_error_eq`
- `NoGuardFPModel.model_mul_signedRelErrorWitness`
- `NoGuardFPModel.model_div_signedRelErrorWitness`
- `FloatingPointFormat.normalizedExponentRepresentation`
- `FloatingPointFormat.normalizedExponentRepresentation_normalizedSystem`
- `FloatingPointFormat.normalizedSystem_exists_normalizedExponentRepresentation`
- `FloatingPointFormat.normalizedSystem_iff_exists_normalizedExponentRepresentation`
- `FloatingPointFormat.normalizedExponentRepresentation_abs_lower_power`
- `FloatingPointFormat.normalizedExponentRepresentation_abs_lt_beta_pow`
- `FloatingPointFormat.fergusonExponentCondition`
- `FloatingPointFormat.fergusonExponentCondition_left_normalized`
- `FloatingPointFormat.fergusonExponentCondition_right_normalized`
- `FloatingPointFormat.fergusonExponentCondition_sub_normalized`
- `FloatingPointFormat.fergusonExponentCondition_sub_not_finiteUnderflowRange`
- `FloatingPointFormat.fergusonExponentCondition_sub_not_finiteOverflowRange`
- `FloatingPointFormat.betaR_zpow_add_one_le_of_two_mul`
- `FloatingPointFormat.normalizedExponentRepresentation_sub_exponent_gap_le_one`
- `FloatingPointFormat.normalizedValue_sub_fergusonCondition_sign_eq`
- `FloatingPointFormat.fergusonExponentCondition_exponent_gap_le_one`
- `FloatingPointFormat.fergusonExponentCondition_same_sign_and_exponent_gap`
- `FloatingPointFormat.fergusonExponentCondition_same_sign_exponent_cases`
- `FloatingPointFormat.alignedSameExponentSubtractionValue`
- `FloatingPointFormat.normalizedValue_sub_sameSign_sameExponent_eq_aligned`
- `FloatingPointFormat.sameExponentMantissaDiffInt`
- `FloatingPointFormat.sameExponentMantissaDiffInt_cast`
- `FloatingPointFormat.sameExponentMantissaDiffInt_natAbs_lt_mantissaBound`
- `FloatingPointFormat.minNormalMantissa_mul_beta_eq_mantissaBound`
- `FloatingPointFormat.sameExponentRenormalizationWitness`
- `FloatingPointFormat.sameExponentSubnormalEndpointWitness`
- `FloatingPointFormat.sameExponent_shift_search`
- `FloatingPointFormat.scaledIntegerValue_finiteSystem_of_natAbs_lt_mantissaBound`
- `FloatingPointFormat.sameExponentFiniteDifferenceWitness`
- `FloatingPointFormat.sameExponentFiniteDifferenceWitness_of_normalizedMantissas`
- `FloatingPointFormat.normalizedValue_eq_subnormalValue_mul_beta_pow_of_subExponent_eq_emin`
- `FloatingPointFormat.guardDigitTailMantissa_eq_natAbs_of_natAbs_lt_mantissaBound`
- `FloatingPointFormat.guardDigitRoundedCoeff_eq_self_of_natAbs_lt_mantissaBound`
- `FloatingPointFormat.guardDigitRoundedSameExponentSubtractionValue`
- `FloatingPointFormat.normalizedValue_sub_sameSign_sameExponent_eq_guardDigitRounded`
- `FloatingPointFormat.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_natAbs_eq_zero`
- `FloatingPointFormat.normalizedValue_mul_beta_predExponent_eq`
- `FloatingPointFormat.normalizedValue_mul_beta_pow_subExponent_eq`
- `FloatingPointFormat.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_normalizedDiff`
- `FloatingPointFormat.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_beta_mul_normalizedDiff`
- `FloatingPointFormat.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_beta_pow_mul_normalizedDiff`
- `FloatingPointFormat.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_renormalizationWitness`
- `FloatingPointFormat.normalizedValue_sub_sameSign_sameExponent_finiteSystem_at_emin_of_natAbs_lt_minNormalMantissa`
- `FloatingPointFormat.normalizedValue_sub_sameSign_sameExponent_finiteSystem_at_shifted_emin_of_natAbs_mul_beta_pow_lt_minNormalMantissa`
- `FloatingPointFormat.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_subnormalEndpointWitness`
- `FloatingPointFormat.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_finiteDifferenceWitness`
- `FloatingPointFormat.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_normalizedMantissas`
- `FloatingPointFormat.sameExponentSubnormalEndpointWitness_of_emin_natAbs_lt_minNormalMantissa`
- `FloatingPointFormat.sameExponentFiniteDifferenceWitness_of_emin_natAbs_lt_minNormalMantissa`
- `FloatingPointFormat.guardAlignedMantissaDiff`
- `FloatingPointFormat.guardAlignedMantissaDiffInt`
- `FloatingPointFormat.guardAlignedMantissaDiffInt_cast`
- `FloatingPointFormat.alignedAdjacentExponentSubtractionValue`
- `FloatingPointFormat.normalizedValue_sub_sameSign_adjacentExponent_eq_aligned`
- `FloatingPointFormat.alignedAdjacentExponentSubtractionValue_finiteSystem_of_natAbs_lt_mantissaBound`
- `FloatingPointFormat.normalizedValue_sub_sameSign_adjacentExponent_finiteSystem_of_natAbs_lt_mantissaBound`
- `FloatingPointFormat.alignedAdjacentExponentSubtractionValue_abs`
- `FloatingPointFormat.guardAlignedMantissaDiff_abs_lt_minNormalMantissa_of_fergusonAdjacent`
- `FloatingPointFormat.guardAlignedMantissaDiffInt_abs_lt_minNormalMantissa_of_fergusonAdjacent`
- `FloatingPointFormat.guardAlignedMantissaDiffInt_natAbs_lt_minNormalMantissa_of_fergusonAdjacent`
- `FloatingPointFormat.guardAlignedMantissaDiffInt_pos_of_adjacentNormalizedMantissas`
- `FloatingPointFormat.guardAlignedMantissaDiffInt_natAbs_lt_mantissaBound_of_sterbenzAdjacent`
- `FloatingPointFormat.normalizedValue_sub_positive_adjacentExponent_finiteSystem_of_sterbenzAdjacent`
- `FloatingPointFormat.sterbenzRatioCondition_positive_normalized_exponent_gap_le_one`
- `FloatingPointFormat.normalizedValue_sub_positive_finiteSystem_of_sterbenzRatioCondition`
- `FloatingPointFormat.normalizedSystem_sub_finiteSystem_of_sterbenzRatioCondition`
- `FloatingPointFormat.subnormalValue_false_pos`
- `FloatingPointFormat.subnormalValue_true_neg`
- `FloatingPointFormat.subnormalValue_sub_sameSign_finiteSystem_of_subnormalMantissas`
- `FloatingPointFormat.subnormalSystem_sub_finiteSystem_of_sterbenzRatioCondition`
- `FloatingPointFormat.normalizedValue_sub_subnormalValue_positive_finiteSystem_of_sterbenzRatioCondition`
- `FloatingPointFormat.normalizedSystem_sub_subnormalSystem_finiteSystem_of_sterbenzRatioCondition`
- `FloatingPointFormat.subnormalSystem_sub_normalizedSystem_finiteSystem_of_sterbenzRatioCondition`
- `FloatingPointFormat.finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition`
- `FloatingPointFormat.guardDigitLeadingDigit`
- `FloatingPointFormat.guardDigitTailMantissa`
- `FloatingPointFormat.guardDigitLeadingDigit_eq_zero_of_natAbs_lt_minNormalMantissa`
- `FloatingPointFormat.guardDigitTailMantissa_eq_natAbs_of_natAbs_lt_minNormalMantissa`
- `FloatingPointFormat.guardDigitLeadingDigit_eq_zero_of_fergusonAdjacent`
- `FloatingPointFormat.guardDigitTailMantissa_eq_natAbs_of_fergusonAdjacent`
- `FloatingPointFormat.guardDigitRoundedCoeff`
- `FloatingPointFormat.guardDigitRoundedCoeff_eq_self_of_natAbs_lt_minNormalMantissa`
- `FloatingPointFormat.guardDigitRoundedCoeff_eq_self_of_fergusonAdjacent`
- `FloatingPointFormat.guardDigitRoundedAdjacentExponentSubtractionValue`
- `FloatingPointFormat.normalizedValue_sub_sameSign_adjacentExponent_eq_guardDigitRounded_of_fergusonAdjacent`
- `FloatingPointFormat.guardAlignedMantissaDiff_abs_lt_minNormalMantissa_of_fergusonAdjacent_reversed`
- `FloatingPointFormat.guardAlignedMantissaDiffInt_abs_lt_minNormalMantissa_of_fergusonAdjacent_reversed`
- `FloatingPointFormat.guardAlignedMantissaDiffInt_natAbs_lt_minNormalMantissa_of_fergusonAdjacent_reversed`
- `FloatingPointFormat.normalizedValue_sub_sameSign_reversedAdjacentExponent_eq_neg_guardDigitRounded_of_fergusonAdjacent`
- `FloatingPointFormat.guardDigitRoundedBranchSubtractionValue`
- `FloatingPointFormat.guardDigitRoundedBranchSubtractionValue_eq_sub_of_ferguson`
- `FloatingPointFormat.guardDigitBranchSubtractionModel`
- `FloatingPointFormat.guardDigitBranchSubtractionModel_guardDigitSubtractionModel`
- `FloatingPointFormat.guardDigitBranchSubtractionModel_exact_of_fergusonCondition`
- `FloatingPointFormat.GuardDigitBranchSubtractionData`
- `FloatingPointFormat.GuardDigitBranchSubtractionData.exponent_cases`
- `FloatingPointFormat.GuardDigitBranchSubtractionData.branchValue_eq_sub`
- `FloatingPointFormat.guardDigitRoundedBranchSubtractionValue_finiteSystem_of_ferguson`
- `FloatingPointFormat.GuardDigitBranchSubtractionData.branchValue_finiteSystem`
- `FloatingPointFormat.guardDigitBranchSubtractionRoutine`
- `FloatingPointFormat.guardDigitBranchSubtractionRoutine_eq_sub_of_data`
- `FloatingPointFormat.guardDigitBranchSubtractionRoutine_branchModel`
- `FloatingPointFormat.guardDigitBranchSubtractionRoutine_guardDigitSubtractionModel`
- `FloatingPointFormat.guardDigitBranchSubtractionRoutine_exact_of_fergusonCondition`
- `FloatingPointFormat.guardDigitBranchSubtractionRoutine_finiteSystem_of_data`
- `FloatingPointFormat.guardDigitBranchSubtractionRoutine_finiteSystem_of_fergusonCondition`
- `FloatingPointFormat.guardDigitSubtractionModel`
- `FloatingPointFormat.guardDigitSubtractionModel_exact_of_fergusonCondition`
- `FloatingPointFormat.finiteRoundToEvenOp_sub_sameSign_sameExponent_eq_exact`
- `FloatingPointFormat.finiteRoundToEvenOp_sub_positive_adjacentExponent_eq_exact_of_sterbenzAdjacent`
- `FloatingPointFormat.finiteRoundToEvenOp_sub_positive_eq_exact_of_sterbenzRatioCondition`
- `FloatingPointFormat.finiteRoundToEvenOp_sub_normalizedSystem_eq_exact_of_sterbenzRatioCondition`
- `FloatingPointFormat.finiteRoundToEvenOp_sub_sameSign_subnormal_eq_exact`
- `FloatingPointFormat.finiteRoundToEvenOp_sub_subnormalSystem_eq_exact_of_sterbenzRatioCondition`
- `FloatingPointFormat.finiteRoundToEvenOp_sub_normalizedSystem_subnormalSystem_eq_exact_of_sterbenzRatioCondition`
- `FloatingPointFormat.finiteRoundToEvenOp_sub_subnormalSystem_normalizedSystem_eq_exact_of_sterbenzRatioCondition`
- `FloatingPointFormat.finiteRoundToEvenOp_sub_finiteSystem_eq_exact_of_sterbenzRatioCondition`
- `heronSemiperimeter`
- `heronRadicand`
- `heronArea`
- `kahanHeronRadicand`
- `kahanHeronArea`
- `finiteKahanHeronAB`
- `finiteKahanHeronBC`
- `finiteKahanHeronBplusC`
- `finiteKahanHeronFactor1`
- `finiteKahanHeronFactor2`
- `finiteKahanHeronFactor3`
- `finiteKahanHeronFactor4`
- `finiteKahanHeronProduct12`
- `finiteKahanHeronProduct123`
- `finiteKahanHeronRadicand`
- `finiteKahanHeronSqrt`
- `finiteKahanHeronArea`
- `kahanHeronTraceStandardModel`
- `kahanHeronExpandedRadicand`
- `kahanOrderedTriangleSides`
- `kahanHeronRadicand_eq_sixteen_mul_heronRadicand`
- `heronRadicand_pos_of_kahanOrderedTriangleSides`
- `kahanHeronRadicand_pos_of_kahanOrderedTriangleSides`
- `kahanHeronFactor_a_add_b_add_c_pos`
- `kahanHeronFactor_b_sub_c_pos`
- `kahanHeronFactor_b_add_c_pos`
- `kahanHeronFactor_c_sub_a_sub_b_pos`
- `kahanHeronFactor_c_add_a_sub_b_pos`
- `kahanHeronFactor_a_add_b_sub_c_pos`
- `kahanHeronExactFactors_pos_of_kahanOrderedTriangleSides`
- `kahanHeronArea_sq_eq_heronRadicand_of_kahanOrderedTriangleSides`
- `kahanOrderedTriangleSides_sterbenzRatioCondition_a_b`
- `finiteRoundToEvenOp_sub_a_b_eq_exact_of_kahanOrderedTriangleSides`
- `finiteKahanHeronAB_eq_exact_of_kahanOrderedTriangleSides`
- `finiteKahanHeronBC_standardModel_lt_of_finiteNormalRange`
- `finiteKahanHeronBplusC_standardModel_lt_of_finiteNormalRange`
- `finiteKahanHeronFactor1_standardModel_lt_of_finiteNormalRange`
- `finiteKahanHeronFactor2_standardModel_lt_of_finiteNormalRange`
- `finiteKahanHeronFactor2_standardModel_lt_of_finiteNormalRange_exactAB`
- `finiteKahanHeronFactor3_standardModel_lt_of_finiteNormalRange`
- `finiteKahanHeronFactor3_standardModel_lt_of_finiteNormalRange_exactAB`
- `finiteKahanHeronFactor4_standardModel_lt_of_finiteNormalRange`
- `finiteKahanHeronProduct12_standardModel_lt_of_finiteNormalRange`
- `finiteKahanHeronProduct123_standardModel_lt_of_finiteNormalRange`
- `finiteKahanHeronRadicand_standardModel_lt_of_finiteNormalRange`
- `finiteKahanHeronSqrt_standardModel_lt_of_finiteNormalRange`
- `finiteKahanHeronArea_standardModel_lt_of_finiteNormalRange`
- `finiteKahanHeronTrace_standardModel_lt_of_finiteNormalRange`
- `kahanHeronTraceStandardModel_radicand_eq_expanded`
- `kahanHeronTraceStandardModel_area_eq_expanded`
- `kahanHeronBplusCRelativeDistortion`
- `kahanHeronBminusCRelativeDistortion`
- `kahanHeronRadicandLocalFactorProduct`
- `kahanHeronRadicandLocalErrors`
- `finiteFormatUnitRoundoffModel`
- `kahanHeronRatio_b_add_c_abs_le_one`
- `kahanHeronRatio_b_sub_c_abs_le_one`
- `kahanHeronScaled_b_add_c_delta_abs_le_unitRoundoff`
- `kahanHeronScaled_b_sub_c_delta_abs_le_unitRoundoff`
- `kahanHeronArea_pos_of_kahanOrderedTriangleSides`
- `kahanHeronExpandedRadicand_eq_exact_mul_local_factors`
- `kahanHeronRadicandLocalErrors_abs_le_unitRoundoff`
- `kahanHeronTraceStandardModel_radicand_rel_error_le_gamma9`
- `kahanHeronTraceStandardModel_area_eq_gamma9_radicand`
- `kahanHeronTraceStandardModel_area_eq_kahanArea_mul_sqrt_gamma9`
- `sqrt_one_add_sub_one_abs_le_abs`
- `three_local_factors_abs_sub_one_le`
- `kahanHeronTraceStandardModel_area_relError_le_gamma9_unitRoundoff`
- `finiteKahanHeronArea_relError_le_gamma9_unitRoundoff_of_finiteNormalRange`
- `leadingDigitOfIndex`
- `logarithmicLeadingDigitMass`
- `logarithmicLeadingDigitMass_eq_log_div`
- `logarithmicLeadingDigitMass_eq_log_one_add_inv`
- `logarithmicIntervalMass`
- `logarithmicLeadingDigitMass_eq_intervalMass`
- `logarithmicIntervalMass_mul_base_pow`
- `logarithmicIntervalMass_mul_base_zpow`
- `logarithmicLeadingDigitMass_scaled_bin`
- `logarithmicLeadingDigitMass_scaled_bin_zpow`
- `logarithmicLeadingDigitMass_nonneg`
- `logarithmicLeadingDigitMass_succ_lt`
- `sum_logarithmicLeadingDigitMass_eq_one`
- `logarithmicLeadingDigitProbability`
- `logarithmicLeadingDigitProbability_prob_eq_log_div`
- `logarithmicLeadingDigitProbability_prob_eq_log_one_add_inv`
- `decimalLogarithmicLeadingDigitProbability_prob_eq`
- `decimalLogarithmicLeadingDigitProbability_prob_eq_log_one_add_inv`
- `decimalLogarithmicLeadingDigitProbability_first_gt_last`
- `decimalLogarithmicLeadingDigitProbability_nonuniform`
- `statisticalRoundingErrorSum`
- `StatisticalRoundingErrorModel`
- `StatisticalRoundingErrorModel.expectation_sum_eq_zero`
- `StatisticalRoundingErrorModel.expectation_sum_sq_eq_sum_second_moments`
- `StatisticalRoundingErrorModel.expectation_sum_sq_le_card_mul_unit_sq`
- `StatisticalRoundingErrorModel.rms_sum_le_sqrt_card_mul_unit`
- `levelIndexForward`
- `levelIndexBackward`
- `levelIndexForward_succ`
- `levelIndexBackward_succ`
- `levelIndexBackward_forward`
- `LevelIndexCode`
- `LevelIndexCode.index`
- `LevelIndexCode.value`
- `LevelIndexCode.reciprocalValue`
- `LevelIndexCode.frac_mem_unit_interval`
- `LevelIndexCode.backward_value_eq_frac`
- `LevelIndexCode.value_pos_of_pos_level`
- `LevelIndexCode.reciprocalValue_pos_of_pos_level`
- `LevelIndexCode.reciprocalValue_mul_value_of_pos_level`
- `LevelIndexCode.value_mul_reciprocalValue_of_pos_level`
- `unitRoundoffProbeExact`
- `unitRoundoffProbeExact_eq_zero`
- `codySineTestExact`
- `codySineReducedArgument`
- `codySineDisplayedTableMagnitude17`
- `codySineDisplayedTableDecimal17`
- `codySineReducedArgument_pos`
- `codySineReducedArgument_lt_one_hundredth`
- `codySineReducedArgument_abs_lt_one_hundredth`
- `codySineTestExact_eq_neg_sin_reducedArgument`
- `codySineTestExact_neg`
- `codySineTestExact_abs_lt_one_hundredth`
- `sineTaylorOdd5`
- `sineTaylorOdd5_eq`
- `sineTaylorOdd5_abs_error_le_next`
- `codySineReducedArgument_sineTaylorOdd5_abs_error_lt_one_e20`
- `codySineTestExact_sineTaylorOdd5_abs_error_lt_one_e20`
- `codySineTaylorOdd5_displayedMagnitude_abs_error_lt_41e21`
- `codySineTestExact_displayedTableDecimal17_abs_error_lt_half_last_place`
- `codyPowerBase`
- `codyPowerExponent`
- `codyPowerTestExact`
- `codyPowerExpLogPath`
- `codyPowerDisplayedDecimal21`
- `codyPowerDisplayedTableDecimal17`
- `codyPowerBase_pos`
- `codyPowerExpLogPath_eq_exact`
- `codyPowerTestExact_displayedDecimal21_abs_error_lt_half_last_place`
- `codyPowerTestExact_displayedTableDecimal17_abs_error_lt_half_last_place`
- `exp_absolute_error_relative_error_eq`
- `exp_absolute_error_relative_error_abs_lt_101_mul_abs`
- `karpinskiGuardDigitProbeA`
- `karpinskiGuardDigitProbeB`
- `karpinskiGuardDigitFiniteProbeA`
- `karpinskiGuardDigitFiniteProbeB`
- `karpinskiGuardDigitProbeA_eq_zero`
- `karpinskiGuardDigitProbeB_eq_zero`
- `karpinskiGuardDigitProbes_equal`
- `FloatingPointFormat.decimalOneDigitThreeExponent_karpinski_div_nine_twentySeven`
- `FloatingPointFormat.decimalOneDigitThreeExponent_karpinski_mul_three_tenths_three_exact`
- `FloatingPointFormat.decimalOneDigitThreeExponent_karpinskiProbeA_eq_neg_one_tenth`
- `FloatingPointFormat.decimalOneDigitThreeExponent_karpinskiProbeB_eq_neg_one_tenth`
- `FloatingPointFormat.decimalOneDigitThreeExponent_karpinskiProbes_equal`
- `fusedMultiplyAddExact`
- `FloatingPointFormat.finiteRoundToEvenFMA`
- `FloatingPointFormat.finiteRoundToModeFMA`
- `FloatingPointFormat.finiteRoundToModeFMA_nearestEven`
- `FloatingPointFormat.finiteRoundToEvenFMA_eq_round_exact`
- `FloatingPointFormat.finiteRoundToEvenFMA_eq_exact_of_finiteSystem`
- `FloatingPointFormat.finiteRoundToEvenFMA_standardModel_lt_of_finiteNormalRange`
- `FloatingPointFormat.finiteRoundToEvenFMA_inverseRelErrorWitness_of_finiteNormalRange`
- `FloatingPointFormat.finiteRoundTowardZero_le_of_nonneg`
- `FloatingPointFormat.le_finiteRoundTowardZero_of_nonpos`
- `FloatingPointFormat.finiteRoundTowardZero_error_nonpos_of_nonneg`
- `FloatingPointFormat.finiteRoundTowardZero_error_nonneg_of_nonpos`
- `FloatingPointFormat.finiteRoundToModeOp_towardZero_error_nonpos_of_exact_nonneg`
- `FloatingPointFormat.finiteRoundToModeOp_towardZero_error_nonneg_of_exact_nonpos`
- `FloatingPointFormat.finiteRoundTowardZero_sum_errors_nonpos_of_nonneg`
- `decimalScale`
- `decimalScale_pos`
- `decimalChopToPlaces`
- `decimalChopToPlaces_le`
- `decimalChopToPlaces_error_nonpos`
- `decimalChopToPlaces_error_nonneg`
- `decimalChopToPlaces_abs_error_lt_scale_inv`
- `decimalChopThree`
- `decimalChopThree_le`
- `decimalChopThree_error_nonpos`
- `decimalChopThree_error_nonneg`
- `decimalChopThree_abs_error_lt_one_thousandth`
- `decimalChopThree_grid_eq`
- `decimalChopThree_initial_index`
- `decimalChopThree_sum_errors_nonpos`
- `FloatingPointFormat.nearestAdjacentRoundToOdd`
- `FloatingPointFormat.nearestAdjacentRoundToOdd_eq_left_of_left_closer`
- `FloatingPointFormat.nearestAdjacentRoundToOdd_eq_right_of_right_closer`
- `FloatingPointFormat.nearestAdjacentRoundToOdd_eq_right_of_tie_even`
- `FloatingPointFormat.nearestAdjacentRoundToOdd_eq_left_of_tie_odd`
- `FloatingPointFormat.decimal_2445_roundToEven_two_places`
- `FloatingPointFormat.decimal_244_roundToEven_one_place`
- `FloatingPointFormat.decimal_2445_roundToEven_chain`
- `FloatingPointFormat.decimal_2445_roundToOdd_two_places`
- `FloatingPointFormat.decimal_245_roundToOdd_one_place`
- `FloatingPointFormat.decimal_2445_roundToOdd_chain`
- `FloatingPointFormat.decimal_105_roundToEven_one_place`
- `FloatingPointFormat.decimal_095_roundToEven_one_place`
- `FloatingPointFormat.decimalOnePlaceRoundToEvenAddSubFromOne`
- `FloatingPointFormat.decimalOnePlaceRoundToEvenAddSubFromOne_eq_one`
- `FloatingPointFormat.decimalOnePlaceRoundToEven_reiserKnuth_stable_from_one`
- `FloatingPointFormat.decimal_105_roundToOdd_one_place`
- `FloatingPointFormat.decimal_115_roundToOdd_one_place`
- `FloatingPointFormat.decimalOnePlaceRoundToOddAddSubFromOne`
- `FloatingPointFormat.decimalOnePlaceRoundToOddAddSubFromOne_eq_eleven_tenths`
- `FloatingPointFormat.decimalOnePlaceRoundToOdd_reiserKnuth_stable_after_first_step`
- `FloatingPointFormat.decimal_105_roundAway_one_place`
- `FloatingPointFormat.decimal_115_roundAway_one_place`
- `FloatingPointFormat.decimalOnePlaceRoundAwayAddSubFromOne`
- `FloatingPointFormat.decimalOnePlaceRoundAwayAddSubFromElevenTenths`
- `FloatingPointFormat.decimalOnePlaceRoundAway_drift_first_two_steps`
- `FloatingPointFormat.decimalOneDigitTwoExponentFormat`
- `FloatingPointFormat.decimalOneDigitTwoExponentFormat_normalizedExponentRepresentation_four`
- `FloatingPointFormat.decimalOneDigitTwoExponentFormat_normalizedExponentRepresentation_neg_four`
- `FloatingPointFormat.decimalOneDigitTwoExponentFormat_normalizedExponentRepresentation_six`
- `FloatingPointFormat.decimalOneDigitTwoExponentFormat_normalizedExponentRepresentation_neg_eight`
- `FloatingPointFormat.decimalOneDigitTwoExponentFormat_normalizedExponentRepresentation_ten`
- `FloatingPointFormat.decimalOneDigitTwoExponentFormat_normalizedExponentRepresentation_twenty`
- `FloatingPointFormat.decimalOneDigitTwoExponentFormat_finiteSystem_four`
- `FloatingPointFormat.decimalOneDigitTwoExponentFormat_finiteSystem_neg_four`
- `FloatingPointFormat.decimalOneDigitTwoExponentFormat_finiteSystem_six`
- `FloatingPointFormat.decimalOneDigitTwoExponentFormat_finiteSystem_neg_eight`
- `FloatingPointFormat.decimalOneDigitTwoExponentFormat_finiteSystem_ten`
- `FloatingPointFormat.decimalOneDigitTwoExponentFormat_finiteSystem_twenty`
- `FloatingPointFormat.decimalOneDigitTwoExponent_add_ten_four_rounds_to_ten`
- `FloatingPointFormat.decimalOneDigitTwoExponent_add_ten_neg_four_exact`
- `FloatingPointFormat.decimalOneDigitTwoExponent_add_four_neg_four_exact`
- `FloatingPointFormat.decimalOneDigitTwoExponent_add_ten_zero_exact`
- `FloatingPointFormat.decimalOneDigitTwoExponent_roundToEven_add_nonassociative`
- `FloatingPointFormat.decimalOneDigitTwoExponent_sub_ten_neg_eight_rounds_to_twenty`
- `FloatingPointFormat.decimalOneDigitTwoExponent_sub_ten_neg_four_rounds_to_ten`
- `FloatingPointFormat.decimalOneDigitTwoExponent_sub_ten_four_exact`
- `FloatingPointFormat.decimalOneDigitTwoExponent_sub_neg_four_four_exact`
- `FloatingPointFormat.decimalOneDigitTwoExponent_roundToEven_sub_nonassociative`
- `FloatingPointFormat.decimalOneDigitThreeExponentFormat`
- `FloatingPointFormat.decimalOneDigitThreeExponentFormat_normalizedExponentRepresentation_one_tenth`
- `FloatingPointFormat.decimalOneDigitThreeExponentFormat_normalizedExponentRepresentation_one_fifth`
- `FloatingPointFormat.decimalOneDigitThreeExponentFormat_normalizedExponentRepresentation_three_tenths`
- `FloatingPointFormat.decimalOneDigitThreeExponentFormat_normalizedExponentRepresentation_two_fifths`
- `FloatingPointFormat.decimalOneDigitThreeExponentFormat_normalizedExponentRepresentation_three_fifths`
- `FloatingPointFormat.decimalOneDigitThreeExponentFormat_normalizedExponentRepresentation_one`
- `FloatingPointFormat.decimalOneDigitThreeExponentFormat_normalizedExponentRepresentation_two`
- `FloatingPointFormat.decimalOneDigitThreeExponentFormat_normalizedExponentRepresentation_three`
- `FloatingPointFormat.decimalOneDigitThreeExponentFormat_normalizedExponentRepresentation_ten`
- `FloatingPointFormat.decimalOneDigitThreeExponentFormat_finiteSystem_one_tenth`
- `FloatingPointFormat.decimalOneDigitThreeExponentFormat_finiteSystem_one`
- `FloatingPointFormat.decimalOneDigitThreeExponentFormat_finiteSystem_three_tenths`
- `FloatingPointFormat.decimalOneDigitThreeExponentFormat_finiteSystem_two_fifths`
- `FloatingPointFormat.decimalOneDigitThreeExponentFormat_finiteSystem_ten`
- `FloatingPointFormat.decimalOneDigitThreeExponent_mul_one_fifth_three_fifths_rounds_to_one_tenth`
- `FloatingPointFormat.decimalOneDigitThreeExponent_mul_three_fifths_three_rounds_to_two`
- `FloatingPointFormat.decimalOneDigitThreeExponent_mul_one_tenth_three_exact`
- `FloatingPointFormat.decimalOneDigitThreeExponent_mul_one_fifth_two_exact`
- `FloatingPointFormat.decimalOneDigitThreeExponent_roundToEven_mul_nonassociative`
- `FloatingPointFormat.decimalOneDigitThreeExponent_div_one_tenth_one_tenth_exact`
- `FloatingPointFormat.decimalOneDigitThreeExponent_div_one_one_tenth_exact`
- `FloatingPointFormat.decimalOneDigitThreeExponent_div_one_tenth_one_exact`
- `FloatingPointFormat.decimalOneDigitThreeExponent_roundToEven_div_nonassociative`
- `FloatingPointFormat.nearestAdjacentRoundToEven_eq_left_or_right`
- `FloatingPointFormat.left_le_nearestAdjacentRoundToEven`
- `FloatingPointFormat.nearestAdjacentRoundToEven_le_right`
- `FloatingPointFormat.nearestAdjacentRoundToEven_monotone_on_ordered_bracket`
- `FloatingPointFormat.finiteRoundToEvenOp_sub_eq_exact_of_guardDigitBranchSubtractionData`
- `FloatingPointFormat.finiteRoundToEvenOp_sub_eq_exact_of_fergusonCondition`
- `FloatingPointFormat.sterbenzRatioCondition`
- `FloatingPointFormat.sterbenzRatioCondition_y_pos`
- `FloatingPointFormat.sterbenzRatioCondition_x_pos`
- `FloatingPointFormat.sterbenzRatioCondition_symm`
- `FloatingPointFormat.sterbenzRatioCondition_abs_sub_lt_left`
- `FloatingPointFormat.sterbenzRatioCondition_abs_sub_lt_right`
- `FloatingPointFormat.sterbenzRatioCondition_abs_sub_lt_min`
- `FloatingPointFormat.decimalSingleDigitFormat`
- `FloatingPointFormat.decimalSingleDigitFormat_normalizedExponentRepresentation_four`
- `FloatingPointFormat.decimalSingleDigitFormat_normalizedExponentRepresentation_five`
- `FloatingPointFormat.decimalSingleDigitFormat_normalizedExponentRepresentation_nine`
- `FloatingPointFormat.decimalSingleDigitFormat_sterbenzRatioCondition_nine_five`
- `FloatingPointFormat.decimalSingleDigitFormat_not_fergusonExponentCondition_nine_five`
- `FloatingPointFormat.decimalSingleDigitFormat_sterbenzRatio_not_ferguson`
- `FloatingPointFormat.sterbenzFergusonBridgeCondition`
- `FloatingPointFormat.sterbenzFergusonBridgeCondition_ratio`
- `FloatingPointFormat.sterbenzFergusonBridgeCondition_ferguson`
- `FloatingPointFormat.guardDigitSubtractionModel_exact_of_sterbenzBridge`
- `IeeeRoundingMode`
- `IeeeExceptionFlag`
- `IeeeValue`
- `IeeeValue.isFinite`
- `IeeeValue.toReal?`
- `IeeeValue.finite_isFinite`
- `IeeeValue.posZero_isFinite`
- `IeeeValue.negZero_isFinite`
- `IeeeValue.toReal?_finite`
- `IeeeValue.toReal?_posZero`
- `IeeeValue.toReal?_negZero`
- `IeeeValue.isFinite_iff_exists`
- `IeeeOperationResult`
- `IeeeOperationResult.finiteNoFlags`
- `IeeeOperationResult.valueNoFlags`
- `IeeeOperationResult.hasFlag`
- `IeeeOperationResult.noFlags`
- `IeeeOperationResult.isFinite`
- `IeeeOperationResult.finiteNoFlags_value`
- `IeeeOperationResult.valueNoFlags_value`
- `IeeeOperationResult.finiteNoFlags_noFlags`
- `IeeeOperationResult.valueNoFlags_noFlags`
- `IeeeOperationResult.not_hasFlag_of_noFlags`
- `IeeeOperationResult.finiteNoFlags_not_hasFlag`
- `IeeeOperationResult.valueNoFlags_not_hasFlag`
- `IeeeOperationResult.finiteNoFlags_isFinite`
- `IeeeOperationResult.valueNoFlags_isFinite_iff`
- `IeeeOperationResult.finiteNoFlags_toReal?`
- `IeeeOperationResult.valueNoFlags_toReal?`
- `FloatingPointFormat`
- `FloatingPointFormat.machineEpsilon`
- `FloatingPointFormat.unitRoundoff`
- `FloatingPointFormat.gradualUnderflowEtaBound`
- `FloatingPointFormat.flushToZeroEtaBound`
- `FloatingPointFormat.unitRoundoff_mul_minNormalMagnitude_eq_half_minSubnormalMagnitude`
- `FloatingPointFormat.gradualUnderflowEtaBound_eq_half_minSubnormalMagnitude`
- `FloatingPointFormat.gradualUnderflowEtaBound_pos`
- `FloatingPointFormat.gradualUnderflowEtaBound_nonneg`
- `FloatingPointFormat.flushToZeroEtaBound_pos`
- `FloatingPointFormat.flushToZeroEtaBound_nonneg`
- `FloatingPointFormat.absError_subnormalValue_false_le_half_minSubnormalMagnitude_of_half_cell`
- `FloatingPointFormat.absError_minNormalMagnitude_le_half_minSubnormalMagnitude_of_boundary_half_cell`
- `FloatingPointFormat.exists_finiteSystem_absError_le_half_minSubnormalMagnitude_nonneg_finiteUnderflowRange`
- `FloatingPointFormat.exists_finiteSystem_absError_le_half_minSubnormalMagnitude_finiteUnderflowRange`
- `FloatingPointFormat.finiteUnderflowNoHalfTie`
- `FloatingPointFormat.nearestRoundingToFinite_absError_le_gradualUnderflowEtaBound_of_finiteUnderflowRange`
- `FloatingPointFormat.nearestRoundingToFinite_absError_lt_gradualUnderflowEtaBound_of_finiteUnderflowRange_of_noHalfTie`
- `FloatingPointFormat.ieeeSingleFormat`
- `FloatingPointFormat.ieeeDoubleFormat`
- `FloatingPointFormat.ieeeSingleFormat_params`
- `FloatingPointFormat.ieeeDoubleFormat_params`
- `FloatingPointFormat.ieeeSingleFormat_machineEpsilon`
- `FloatingPointFormat.ieeeSingleFormat_unitRoundoff`
- `FloatingPointFormat.ieeeDoubleFormat_machineEpsilon`
- `FloatingPointFormat.ieeeDoubleFormat_unitRoundoff`
- `FloatingPointFormat.ieeeSingleFormat_ulpAtExponent`
- `FloatingPointFormat.ieeeDoubleFormat_ulpAtExponent`
- `FloatingPointFormat.matlabIeeeDoubleEps`
- `FloatingPointFormat.matlabIeeeDoubleEps_eq_ieeeDoubleFormat_machineEpsilon`
- `FloatingPointFormat.matlabIeeeDoubleEps_eq_two_zpow_neg52`
- `FloatingPointFormat.matlabIeeeDoubleEps_eq_two_mul_ieeeDoubleFormat_unitRoundoff`
- `FloatingPointFormat.fortranEpsilon`
- `FloatingPointFormat.fortranEpsilon_eq_machineEpsilon`
- `FloatingPointFormat.fortranEpsilon_pos`
- `FloatingPointFormat.fortranEpsilon_eq_two_mul_unitRoundoff`
- `FloatingPointFormat.ieeeSingleFormat_fortranEpsilon`
- `FloatingPointFormat.ieeeDoubleFormat_fortranEpsilon`
- `FloatingPointFormat.matlabIeeeDoubleEps_eq_ieeeDoubleFormat_fortranEpsilon`
- `FloatingPointFormat.mantissaInRange`
- `FloatingPointFormat.minNormalMantissa`
- `FloatingPointFormat.maxNormalMantissa`
- `FloatingPointFormat.normalizedMantissa`
- `FloatingPointFormat.subnormalMantissa`
- `FloatingPointFormat.exponentInRange`
- `FloatingPointFormat.normalizedValue`
- `FloatingPointFormat.subnormalValue`
- `FloatingPointFormat.normalizedSystem`
- `FloatingPointFormat.unboundedNormalizedSystem`
- `FloatingPointFormat.subnormalSystem`
- `FloatingPointFormat.finiteSystem`
- `FloatingPointFormat.minNormalMagnitude`
- `FloatingPointFormat.minSubnormalMagnitude`
- `FloatingPointFormat.maxFiniteMagnitude`
- `FloatingPointFormat.finiteNormalRange`
- `FloatingPointFormat.finiteUnderflowRange`
- `FloatingPointFormat.finiteOverflowRange`
- `FloatingPointFormat.digitStringInRange`
- `FloatingPointFormat.normalizedDigitString`
- `FloatingPointFormat.positionalMantissa`
- `FloatingPointFormat.positionalValue`
- `FloatingPointFormat.sameExponentAdjacentNormalized`
- `FloatingPointFormat.boundaryAdjacentNormalized`
- `FloatingPointFormat.adjacentNormalized`
- `FloatingPointFormat.realOrderAdjacentNormalized`
- `FloatingPointFormat.nearestRoundingIn`
- `FloatingPointFormat.nearestRoundingToUnbounded`
- `FloatingPointFormat.nearestRoundingToFinite`
- `FloatingPointFormat.nearestAdjacentRoundAway`
- `FloatingPointFormat.evenMantissa`
- `FloatingPointFormat.nearestAdjacentRoundToEven`
- `FloatingPointFormat.adjacentRoundTowardNegative`
- `FloatingPointFormat.adjacentRoundTowardPositive`
- `FloatingPointFormat.adjacentRoundTowardZero`
- `FloatingPointFormat.normalizedSystem_unboundedNormalizedSystem`
- `FloatingPointFormat.minNormalMantissa_pos`
- `FloatingPointFormat.mantissaBound_pos`
- `FloatingPointFormat.one_lt_beta`
- `FloatingPointFormat.minNormalMantissa_lt_mantissaBound`
- `FloatingPointFormat.normalizedMantissa_pos`
- `FloatingPointFormat.subnormalMantissa_inRange`
- `FloatingPointFormat.one_subnormalMantissa_of_subnormalMantissa`
- `FloatingPointFormat.digitStringInRange_reverse`
- `FloatingPointFormat.positionalMantissa_lt_mantissaBound`
- `FloatingPointFormat.minNormalMantissa_le_positionalMantissa`
- `FloatingPointFormat.positionalMantissa_normalized`
- `FloatingPointFormat.positionalValue_eq_normalizedValue_positionalMantissa`
- `FloatingPointFormat.positionalValue_mem_normalizedSystem`
- `FloatingPointFormat.exists_digitStringInRange_positionalMantissa_eq`
- `FloatingPointFormat.exists_normalizedDigitString_positionalMantissa_eq`
- `FloatingPointFormat.digitStringInRange_eq_of_positionalMantissa_eq`
- `FloatingPointFormat.minNormalMantissa_normalized`
- `FloatingPointFormat.maxNormalMantissa_add_one`
- `FloatingPointFormat.maxNormalMantissa_lt_mantissaBound`
- `FloatingPointFormat.minNormalMantissa_le_maxNormalMantissa`
- `FloatingPointFormat.maxNormalMantissa_normalized`
- `FloatingPointFormat.minNormalMantissa_mem_normalizedSystem`
- `FloatingPointFormat.maxNormalMantissa_mem_normalizedSystem`
- `FloatingPointFormat.betaR_pos`
- `FloatingPointFormat.betaR_nonneg`
- `FloatingPointFormat.betaR_zpow_pos`
- `FloatingPointFormat.betaR_zpow_nonneg`
- `FloatingPointFormat.betaR_zpow_le_zpow_of_le`
- `FloatingPointFormat.machineEpsilon_nonneg`
- `FloatingPointFormat.unitRoundoff_nonneg`
- `FloatingPointFormat.signValue_abs`
- `FloatingPointFormat.normalizedValue_abs`
- `FloatingPointFormat.subnormalValue_abs`
- `FloatingPointFormat.normalizedValue_ne_zero`
- `FloatingPointFormat.unboundedNormalizedSystem_ne_zero`
- `FloatingPointFormat.subnormalValue_ne_zero`
- `FloatingPointFormat.subnormalSystem_ne_zero`
- `FloatingPointFormat.normalizedValue_true_eq_neg_false`
- `FloatingPointFormat.normalizedValue_not_eq_neg`
- `FloatingPointFormat.subnormalValue_not_eq_neg`
- `FloatingPointFormat.normalizedSystem_neg`
- `FloatingPointFormat.unboundedNormalizedSystem_neg`
- `FloatingPointFormat.subnormalSystem_neg`
- `FloatingPointFormat.finiteSystem_neg`
- `FloatingPointFormat.normalizedValue_sameExponent_lt_iff_false`
- `FloatingPointFormat.normalizedValue_sameExponent_lt_iff_true`
- `FloatingPointFormat.normalizedValue_sameExponent_no_between_succ`
- `FloatingPointFormat.normalizedValue_false_pos`
- `FloatingPointFormat.normalizedValue_true_neg`
- `FloatingPointFormat.normalizedValue_abs_lower_mantissa`
- `FloatingPointFormat.minNormalMantissa_scale_eq`
- `FloatingPointFormat.normalizedValue_minNormalMantissa_abs_eq`
- `FloatingPointFormat.normalizedValue_abs_lower_power`
- `FloatingPointFormat.normalizedValue_abs_lt_mantissaBound`
- `FloatingPointFormat.mantissaBound_scale_eq`
- `FloatingPointFormat.maxNormalMantissa_cast`
- `FloatingPointFormat.maxNormalMantissa_scale_eq`
- `FloatingPointFormat.normalizedValue_maxNormalMantissa_abs_eq_sub`
- `FloatingPointFormat.normalizedValue_maxNormalMantissa_abs_eq`
- `FloatingPointFormat.normalizedValue_abs_lt_beta_pow`
- `FloatingPointFormat.normalizedValue_abs_between_beta_powers`
- `FloatingPointFormat.normalizedValue_false_minNormalMantissa_eq`
- `FloatingPointFormat.normalizedValue_false_maxNormalMantissa_eq`
- `FloatingPointFormat.normalizedValue_abs_lower_of_exp_ge`
- `FloatingPointFormat.normalizedValue_abs_le_maxNormalMantissa_same_exp`
- `FloatingPointFormat.normalizedValue_abs_le_maxNormalMantissa_of_exp_le`
- `FloatingPointFormat.normalizedSystem_abs_lower_bound`
- `FloatingPointFormat.normalizedSystem_abs_le_maxNormalMantissa`
- `FloatingPointFormat.normalizedSystem_abs_le_maxFinite_bound`
- `FloatingPointFormat.normalizedSystem_abs_bounds`
- `FloatingPointFormat.minNormalMagnitude_pos`
- `FloatingPointFormat.minSubnormalMagnitude_pos`
- `FloatingPointFormat.minSubnormalMagnitude_le_minNormalMagnitude`
- `FloatingPointFormat.minNormalMagnitude_le_maxFiniteMagnitude`
- `FloatingPointFormat.maxFiniteMagnitude_nonneg`
- `FloatingPointFormat.minSubnormalMagnitude_nonneg`
- `FloatingPointFormat.maxFiniteMagnitude_lt_beta_pow_emax`
- `FloatingPointFormat.minNormalMagnitude_mem_normalizedSystem`
- `FloatingPointFormat.maxFiniteMagnitude_mem_normalizedSystem`
- `FloatingPointFormat.neg_minNormalMagnitude_mem_normalizedSystem`
- `FloatingPointFormat.neg_maxFiniteMagnitude_mem_normalizedSystem`
- `FloatingPointFormat.minNormalMagnitude_mem_finiteSystem`
- `FloatingPointFormat.minNormalMagnitude_mem_unboundedNormalizedSystem`
- `FloatingPointFormat.maxFiniteMagnitude_mem_finiteSystem`
- `FloatingPointFormat.maxFiniteMagnitude_mem_unboundedNormalizedSystem`
- `FloatingPointFormat.neg_minNormalMagnitude_mem_finiteSystem`
- `FloatingPointFormat.neg_minNormalMagnitude_mem_unboundedNormalizedSystem`
- `FloatingPointFormat.neg_maxFiniteMagnitude_mem_finiteSystem`
- `FloatingPointFormat.neg_maxFiniteMagnitude_mem_unboundedNormalizedSystem`
- `FloatingPointFormat.normalizedSystem_finiteNormalRange`
- `FloatingPointFormat.unboundedNormalizedSystem_normalizedSystem_of_finiteNormalRange`
- `FloatingPointFormat.normalizedSystem_not_finiteUnderflowRange`
- `FloatingPointFormat.normalizedSystem_not_finiteOverflowRange`
- `FloatingPointFormat.normalizedSystem_abs_ge_minSubnormalMagnitude`
- `FloatingPointFormat.subnormalValue_abs_lt_min_normal`
- `FloatingPointFormat.subnormalSystem_finiteUnderflowRange`
- `FloatingPointFormat.subnormalSystem_le_minNormalMagnitude`
- `FloatingPointFormat.neg_minNormalMagnitude_le_subnormalSystem`
- `FloatingPointFormat.subnormalSystem_abs_ge_minSubnormalMagnitude`
- `FloatingPointFormat.subnormalSystem_not_finiteOverflowRange`
- `FloatingPointFormat.finiteSystem_zero_or_finiteNormalRange_or_finiteUnderflowRange`
- `FloatingPointFormat.finiteSystem_finiteUnderflowRange_iff_zero_or_subnormalSystem`
- `FloatingPointFormat.finiteSystem_finiteUnderflowRange_ne_zero_iff_subnormalSystem`
- `FloatingPointFormat.finiteSystem_not_finiteOverflowRange`
- `FloatingPointFormat.finiteSystem_abs_le_maxFiniteMagnitude`
- `FloatingPointFormat.finiteSystem_ne_zero_abs_ge_minSubnormalMagnitude`
- `FloatingPointFormat.subnormalValue_false_one_eq`
- `FloatingPointFormat.subnormalValue_one_abs_eq`
- `FloatingPointFormat.minSubnormalMagnitude_mem_subnormalSystem_of_subnormalMantissa_one`
- `FloatingPointFormat.two_mul_minSubnormalMagnitude_le_minNormalMagnitude_of_subnormalMantissa_one`
- `FloatingPointFormat.subnormalValue_false_one_le_of_subnormalMantissa`
- `FloatingPointFormat.subnormalValue_succ_sub`
- `FloatingPointFormat.subnormalValue_succ_spacing`
- `FloatingPointFormat.subnormalValue_boundary_sub`
- `FloatingPointFormat.subnormalValue_boundary_spacing`
- `FloatingPointFormat.normalizedValue_false_lower_power`
- `FloatingPointFormat.normalizedValue_false_lt_beta_pow`
- `FloatingPointFormat.normalizedValue_false_lt_of_exp_lt`
- `FloatingPointFormat.normalizedValue_true_lt_of_exp_lt`
- `FloatingPointFormat.normalizedValue_false_eq_iff`
- `FloatingPointFormat.normalizedValue_true_eq_iff`
- `FloatingPointFormat.normalizedValue_false_ne_true`
- `FloatingPointFormat.normalizedValue_eq_sign_exp_mantissa`
- `FloatingPointFormat.normalizedValue_eq_iff_sign_exp_mantissa`
- `FloatingPointFormat.nat_floor_exact_or_successor_bracket`
- `FloatingPointFormat.exists_unboundedNormalized_or_realOrderAdjacent_bracket_sameExponent`
- `FloatingPointFormat.exists_nearestRoundingToUnbounded_signedRelErrorWitness_sameExponent_positive`
- `FloatingPointFormat.exists_unboundedNormalized_or_realOrderAdjacent_bracket_sameExponent_negative`
- `FloatingPointFormat.exists_nearestRoundingToUnbounded_signedRelErrorWitness_sameExponent_negative`
- `FloatingPointFormat.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_sameExponent_positive`
- `FloatingPointFormat.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_sameExponent_negative`
- `FloatingPointFormat.exists_nearestRoundingToUnbounded_signedRelErrorWitness_powerInterval_positive`
- `FloatingPointFormat.exists_nearestRoundingToUnbounded_signedRelErrorWitness_powerInterval_negative`
- `FloatingPointFormat.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_powerInterval_positive`
- `FloatingPointFormat.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_powerInterval_negative`
- `FloatingPointFormat.exists_nearestRoundingToUnbounded_signedRelErrorWitness_powerBoundary_positive`
- `FloatingPointFormat.exists_nearestRoundingToUnbounded_signedRelErrorWitness_powerBoundary_negative`
- `FloatingPointFormat.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_powerBoundary_positive`
- `FloatingPointFormat.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_powerBoundary_negative`
- `FloatingPointFormat.exists_nearestRoundingToUnbounded_signedRelErrorWitness_powerSlice_positive`
- `FloatingPointFormat.exists_nearestRoundingToUnbounded_signedRelErrorWitness_powerSlice_negative`
- `FloatingPointFormat.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_powerSlice_positive`
- `FloatingPointFormat.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_powerSlice_negative`
- `FloatingPointFormat.exists_powerSliceExponent_positive`
- `FloatingPointFormat.exists_powerSliceExponent_negative`
- `FloatingPointFormat.exists_nearestRoundingToUnbounded_signedRelErrorWitness_positive`
- `FloatingPointFormat.exists_nearestRoundingToUnbounded_signedRelErrorWitness_negative`
- `FloatingPointFormat.exists_nearestRoundingToUnbounded_signedRelErrorWitness_nonzero`
- `FloatingPointFormat.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_positive`
- `FloatingPointFormat.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_negative`
- `FloatingPointFormat.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_nonzero`
- `FloatingPointFormat.normalizedValue_false_le_of_mantissa_le`
- `FloatingPointFormat.normalizedValue_false_le_maxNormalMantissa`
- `FloatingPointFormat.normalizedValue_false_minNormalMantissa_le`
- `FloatingPointFormat.normalizedValue_false_minNormalMantissa_succ_eq_beta_pow`
- `FloatingPointFormat.normalizedValue_false_le_maxNormalMantissa_of_exp_le`
- `FloatingPointFormat.normalizedValue_false_minNormalMantissa_le_of_exp_le`
- `FloatingPointFormat.normalizedValue_sameSign_no_between_succ`
- `FloatingPointFormat.normalizedValue_oppositeSign_no_between_succ`
- `FloatingPointFormat.normalizedValue_no_between_succ`
- `FloatingPointFormat.normalizedValue_boundary_no_between`
- `FloatingPointFormat.machineEpsilon_mul_lower_power_eq`
- `FloatingPointFormat.beta_inv_machineEpsilon_mul_upper_power_eq`
- `FloatingPointFormat.ulpAtExponent`
- `FloatingPointFormat.ulpAtExponent_nonneg`
- `FloatingPointFormat.ulpAtExponent_pos`
- `FloatingPointFormat.ulpAtExponent_one`
- `FloatingPointFormat.ulpAtExponent_eq_machineEpsilon_mul_lower_power`
- `FloatingPointFormat.ulpAtExponent_eq_beta_inv_machineEpsilon_mul_upper_power`
- `FloatingPointFormat.normalizedValue_spacing_bounds`
- `FloatingPointFormat.normalizedValue_wobblingPrecision_bounds`
- `FloatingPointFormat.normalizedValue_succ_sub_sameExponent`
- `FloatingPointFormat.normalizedValue_succ_spacing`
- `FloatingPointFormat.normalizedValue_succ_spacing_eq_ulpAtExponent`
- `FloatingPointFormat.normalizedValue_boundary_sub`
- `FloatingPointFormat.normalizedValue_boundary_spacing`
- `FloatingPointFormat.normalizedValue_boundary_spacing_eq_ulpAtExponent`
- `FloatingPointFormat.normalizedValue_boundary_min_spacing_bounds`
- `FloatingPointFormat.sameExponentAdjacentNormalized_abs_sub`
- `FloatingPointFormat.sameExponentAdjacentNormalized_abs_sub_eq_ulpAtExponent`
- `FloatingPointFormat.boundaryAdjacentNormalized_abs_sub`
- `FloatingPointFormat.adjacentNormalized_abs_sub`
- `FloatingPointFormat.sameExponentAdjacentNormalized_left_mem`
- `FloatingPointFormat.sameExponentAdjacentNormalized_right_mem`
- `FloatingPointFormat.boundaryAdjacentNormalized_left_mem`
- `FloatingPointFormat.boundaryAdjacentNormalized_right_mem`
- `FloatingPointFormat.adjacentNormalized_left_mem`
- `FloatingPointFormat.adjacentNormalized_right_mem`
- `FloatingPointFormat.adjacentNormalized_ne`
- `FloatingPointFormat.adjacentNormalized_endpoint_data`
- `FloatingPointFormat.realOrderAdjacentNormalized_of_adjacentNormalized_no_between`
- `FloatingPointFormat.realOrderAdjacentNormalized_symm`
- `FloatingPointFormat.sameExponentAdjacentNormalized_symm`
- `FloatingPointFormat.boundaryAdjacentNormalized_symm`
- `FloatingPointFormat.adjacentNormalized_symm`
- `FloatingPointFormat.sameExponentAdjacentNormalized_neg`
- `FloatingPointFormat.boundaryAdjacentNormalized_neg`
- `FloatingPointFormat.adjacentNormalized_neg`
- `FloatingPointFormat.sameExponentAdjacentNormalized_no_between`
- `FloatingPointFormat.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized`
- `FloatingPointFormat.boundaryAdjacentNormalized_no_between`
- `FloatingPointFormat.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized`
- `FloatingPointFormat.adjacentNormalized_no_between`
- `FloatingPointFormat.realOrderAdjacentNormalized_of_adjacentNormalized`
- `FloatingPointFormat.realOrderAdjacentNormalized_same_sign_of_representations`
- `FloatingPointFormat.realOrderAdjacentNormalized_false_ordered_exp_ge`
- `FloatingPointFormat.realOrderAdjacentNormalized_false_ordered_exp_le_succ`
- `FloatingPointFormat.realOrderAdjacentNormalized_false_ordered_exp_eq_or_succ`
- `FloatingPointFormat.realOrderAdjacentNormalized_false_ordered_same_exp_mantissa_succ`
- `FloatingPointFormat.realOrderAdjacentNormalized_false_ordered_succ_exp_mantissa_boundary`
- `FloatingPointFormat.realOrderAdjacentNormalized_false_ordered_adjacentNormalized`
- `FloatingPointFormat.realOrderAdjacentNormalized_false_representations_adjacentNormalized`
- `FloatingPointFormat.realOrderAdjacentNormalized_false_of_true_representations`
- `FloatingPointFormat.realOrderAdjacentNormalized_true_representations_adjacentNormalized`
- `FloatingPointFormat.adjacentNormalized_of_realOrderAdjacentNormalized`
- `FloatingPointFormat.sameExponentAdjacentNormalized_spacing_bounds_left`
- `FloatingPointFormat.boundaryAdjacentNormalized_spacing_bounds_left`
- `FloatingPointFormat.adjacentNormalized_spacing_bounds_left`
- `FloatingPointFormat.realOrderAdjacentNormalized_spacing_bounds_left`
- `FloatingPointFormat.boundaryAdjacentNormalized_abs_sub_eq_ulpAtExponent`
- `FloatingPointFormat.adjacentNormalized_abs_sub_eq_ulpAtExponent`
- `FloatingPointFormat.realOrderAdjacentNormalized_relativeSpacing_bounds_left`
- `FloatingPointFormat.ieeeSingleFormat_realOrderAdjacentNormalized_relativeSpacing_bounds_left`
- `FloatingPointFormat.adjacentNormalized_realOrder_spacing_bounds_left`
- `FloatingPointFormat.unitRoundoff_eq_half_machineEpsilon`
- `FloatingPointFormat.nearestRoundingIn_mem`
- `FloatingPointFormat.nearestRoundingIn_minimal`
- `FloatingPointFormat.nearestRoundingIn_neg`
- `FloatingPointFormat.nearestRoundingToFinite_neg`
- `FloatingPointFormat.nearestRoundingIn_self`
- `FloatingPointFormat.nearestRoundingToUnbounded_self`
- `FloatingPointFormat.nearestRoundingToFinite_self`
- `FloatingPointFormat.finiteSystem_zero`
- `FloatingPointFormat.nearestRoundingToFinite_zero`
- `FloatingPointFormat.nearestRoundingToFinite_of_nearestRoundingToUnbounded_of_finite_of_minNormalMagnitude_le`
- `FloatingPointFormat.nearestRoundingToFinite_of_nearestRoundingToUnbounded_of_finite_of_le_neg_minNormalMagnitude`
- `FloatingPointFormat.nearestRoundingToUnbounded_output_finite_of_minNormalMagnitude_le_of_le_maxFiniteMagnitude`
- `FloatingPointFormat.nearestRoundingToUnbounded_output_finite_of_neg_maxFiniteMagnitude_le_of_le_neg_minNormalMagnitude`
- `FloatingPointFormat.nearestRoundingToFinite_output_zero_or_finiteNormalRange_or_finiteUnderflowRange`
- `FloatingPointFormat.nearestRoundingToFinite_output_underflow_zero_or_subnormalSystem`
- `FloatingPointFormat.nearestRoundingToFinite_output_underflow_ne_zero_subnormalSystem`
- `FloatingPointFormat.nearestRoundingToFinite_output_not_finiteOverflowRange`
- `FloatingPointFormat.nearestRoundingToFinite_output_abs_le_maxFiniteMagnitude`
- `FloatingPointFormat.nearestRoundingToFinite_eq_maxFiniteMagnitude_of_gt_maxFiniteMagnitude`
- `FloatingPointFormat.nearestRoundingToFinite_eq_neg_maxFiniteMagnitude_of_lt_neg_maxFiniteMagnitude`
- `FloatingPointFormat.nearestRoundingToFinite_zero_of_abs_le_half_minSubnormalMagnitude`
- `FloatingPointFormat.nearestRoundingToFinite_eq_zero_of_abs_lt_half_minSubnormalMagnitude`
- `FloatingPointFormat.nearestRoundingToFinite_minSubnormalMagnitude_of_half_le_of_le_three_halves`
- `FloatingPointFormat.nearestRoundingToFinite_neg_minSubnormalMagnitude_of_neg_three_halves_le_of_le_neg_half`
- `FloatingPointFormat.nearestRoundingToFinite_subnormalValue_false_of_half_cell`
- `FloatingPointFormat.nearestRoundingToFinite_subnormalValue_true_of_half_cell`
- `FloatingPointFormat.nearestRoundingToFinite_exact_signedRelErrorWitness`
- `FloatingPointFormat.exists_nearestRoundingToFinite_signedRelErrorWitness_zero`
- `FloatingPointFormat.exists_nearestRoundingToFinite_signedRelErrorWitness_positive_finiteNormalRange`
- `FloatingPointFormat.exists_nearestRoundingToFinite_signedRelErrorWitness_negative_finiteNormalRange`
- `FloatingPointFormat.exists_nearestRoundingToFinite_signedRelErrorWitness_finiteNormalRange`
- `FloatingPointFormat.nearestRoundingToFinite_signedRelErrorWitness_of_finiteNormalRange`
- `FloatingPointFormat.nearestRoundingToUnbounded_abs_sub_le_unitRoundoff_mul_rounded_of_realOrderAdjacent_between`
- `FloatingPointFormat.relErrorComputedDenom_le_unitRoundoff_of_abs_sub_le_unitRoundoff_mul_abs`
- `FloatingPointFormat.nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_of_realOrderAdjacent_between`
- `FloatingPointFormat.nearestRoundingToUnbounded_exact_relErrorComputedDenom_le_unitRoundoff`
- `FloatingPointFormat.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_of_realOrderAdjacent_ordered_between`
- `FloatingPointFormat.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_sameExponent_positive`
- `FloatingPointFormat.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_sameExponent_negative`
- `FloatingPointFormat.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_powerInterval_positive`
- `FloatingPointFormat.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_powerInterval_negative`
- `FloatingPointFormat.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_powerBoundary_positive`
- `FloatingPointFormat.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_powerBoundary_negative`
- `FloatingPointFormat.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_powerSlice_positive`
- `FloatingPointFormat.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_powerSlice_negative`
- `FloatingPointFormat.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_positive`
- `FloatingPointFormat.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_negative`
- `FloatingPointFormat.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_nonzero`
- `FloatingPointFormat.exists_nearestRoundingToFinite_relErrorComputedDenom_le_unitRoundoff_positive_finiteNormalRange`
- `FloatingPointFormat.exists_nearestRoundingToFinite_relErrorComputedDenom_le_unitRoundoff_negative_finiteNormalRange`
- `FloatingPointFormat.exists_nearestRoundingToFinite_relErrorComputedDenom_le_unitRoundoff_finiteNormalRange`
- `FloatingPointFormat.nearestRoundingToUnbounded_exact_signedRelErrorWitness`
- `FloatingPointFormat.nearestRoundingIn_abs_sub_le_half_abs_sub_of_between`
- `FloatingPointFormat.nearestRoundingToUnbounded_eq_left_or_right_of_realOrderAdjacent_ordered_between`
- `FloatingPointFormat.nearestRoundingToUnbounded_eq_left_or_right_of_realOrderAdjacent_between`
- `FloatingPointFormat.nearestRoundingToUnbounded_left_of_realOrderAdjacent_ordered_between`
- `FloatingPointFormat.nearestRoundingToUnbounded_right_of_realOrderAdjacent_ordered_between`
- `FloatingPointFormat.exists_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between`
- `FloatingPointFormat.nearestAdjacentRoundAway_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between`
- `FloatingPointFormat.nearestAdjacentRoundAway_signedRelErrorWitness_lt_of_nonneg_between`
- `FloatingPointFormat.nearestAdjacentRoundAway_signedRelErrorWitness_lt_of_nonpos_between`
- `FloatingPointFormat.nearestAdjacentRoundToEven_eq_left_of_left_closer`
- `FloatingPointFormat.nearestAdjacentRoundToEven_eq_right_of_right_closer`
- `FloatingPointFormat.nearestAdjacentRoundToEven_eq_left_of_tie_even`
- `FloatingPointFormat.nearestAdjacentRoundToEven_eq_right_of_tie_odd`
- `FloatingPointFormat.nearestAdjacentRoundToEven_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between`
- `FloatingPointFormat.nearestAdjacentRoundToEven_nearestRoundingToUnbounded_of_sameExponentAdjacentNormalized_ordered_between`
- `FloatingPointFormat.adjacentRoundTowardNegative_eq_right_of_eq_right`
- `FloatingPointFormat.adjacentRoundTowardNegative_eq_left_of_ne_right`
- `FloatingPointFormat.adjacentRoundTowardPositive_eq_left_of_eq_left`
- `FloatingPointFormat.adjacentRoundTowardPositive_eq_right_of_ne_left`
- `FloatingPointFormat.adjacentRoundTowardZero_eq_towardPositive_of_neg`
- `FloatingPointFormat.adjacentRoundTowardZero_eq_towardNegative_of_nonneg`
- `FloatingPointFormat.adjacentRoundTowardNegative_mem_unboundedNormalized`
- `FloatingPointFormat.adjacentRoundTowardPositive_mem_unboundedNormalized`
- `FloatingPointFormat.adjacentRoundTowardZero_mem_unboundedNormalized_of_nonneg_between`
- `FloatingPointFormat.adjacentRoundTowardZero_mem_unboundedNormalized_of_nonpos_between`
- `FloatingPointFormat.adjacentRoundTowardNegative_le_of_ordered_between`
- `FloatingPointFormat.le_adjacentRoundTowardPositive_of_ordered_between`
- `FloatingPointFormat.adjacentRoundTowardZero_nonneg_le_of_nonneg_between`
- `FloatingPointFormat.adjacentRoundTowardZero_le_nonpos_of_nonpos_between`
- `FloatingPointFormat.adjacentRoundTowardZero_abs_le_abs_of_nonneg_between`
- `FloatingPointFormat.adjacentRoundTowardZero_abs_le_abs_of_nonpos_between`
- `FloatingPointFormat.sourceRoundTowardNegativeEvidence`
- `FloatingPointFormat.sourceRoundTowardPositiveEvidence`
- `FloatingPointFormat.sourceRoundTowardZeroEvidence`
- `FloatingPointFormat.sourceRoundTowardNegativeEvidence_unboundedNormalizedSystem`
- `FloatingPointFormat.sourceRoundTowardPositiveEvidence_unboundedNormalizedSystem`
- `FloatingPointFormat.sourceRoundTowardZeroEvidence_unboundedNormalizedSystem`
- `FloatingPointFormat.sourceRoundTowardNegativeEvidence_le`
- `FloatingPointFormat.sourceRoundTowardPositiveEvidence_le`
- `FloatingPointFormat.sourceRoundTowardZeroEvidence_abs_le_abs`
- `FloatingPointFormat.exists_sourceRoundTowardNegativeEvidence_finiteNormalRange`
- `FloatingPointFormat.exists_sourceRoundTowardPositiveEvidence_finiteNormalRange`
- `FloatingPointFormat.exists_sourceRoundTowardZeroEvidence_finiteNormalRange`
- `FloatingPointFormat.finiteNormalRoundTowardNegative`
- `FloatingPointFormat.finiteNormalRoundTowardPositive`
- `FloatingPointFormat.finiteNormalRoundTowardZero`
- `FloatingPointFormat.finiteNormalRoundTowardNegative_sourceRoundTowardNegativeEvidence`
- `FloatingPointFormat.finiteNormalRoundTowardPositive_sourceRoundTowardPositiveEvidence`
- `FloatingPointFormat.finiteNormalRoundTowardZero_sourceRoundTowardZeroEvidence`
- `FloatingPointFormat.finiteNormalRoundTowardNegative_unboundedNormalizedSystem`
- `FloatingPointFormat.finiteNormalRoundTowardPositive_unboundedNormalizedSystem`
- `FloatingPointFormat.finiteNormalRoundTowardZero_unboundedNormalizedSystem`
- `FloatingPointFormat.finiteNormalRoundTowardNegative_le`
- `FloatingPointFormat.le_finiteNormalRoundTowardPositive`
- `FloatingPointFormat.finiteNormalRoundTowardZero_abs_le_abs`
- `FloatingPointFormat.finiteUnderflowRoundTowardZeroNonneg`
- `FloatingPointFormat.finiteUnderflowRoundTowardPositiveNonneg`
- `FloatingPointFormat.finiteUnderflowRoundTowardZeroNonneg_finiteSystem`
- `FloatingPointFormat.finiteUnderflowRoundTowardPositiveNonneg_finiteSystem`
- `FloatingPointFormat.finiteUnderflowRoundTowardZeroNonneg_le`
- `FloatingPointFormat.le_finiteUnderflowRoundTowardPositiveNonneg`
- `FloatingPointFormat.finiteUnderflowRoundTowardZero`
- `FloatingPointFormat.finiteUnderflowRoundTowardPositive`
- `FloatingPointFormat.finiteUnderflowRoundTowardNegative`
- `FloatingPointFormat.finiteUnderflowRoundTowardZero_finiteSystem`
- `FloatingPointFormat.finiteUnderflowRoundTowardPositive_finiteSystem`
- `FloatingPointFormat.finiteUnderflowRoundTowardNegative_finiteSystem`
- `FloatingPointFormat.finiteUnderflowRoundTowardZero_abs_le_abs`
- `FloatingPointFormat.le_finiteUnderflowRoundTowardPositive`
- `FloatingPointFormat.finiteUnderflowRoundTowardNegative_le`
- `FloatingPointFormat.finiteOverflowSaturation_abs_le_abs_of_finiteOverflowRange`
- `FloatingPointFormat.finiteNormalRange_of_not_finiteUnderflowRange_of_not_finiteOverflowRange`
- `FloatingPointFormat.finiteRoundTowardNegative`
- `FloatingPointFormat.finiteRoundTowardPositive`
- `FloatingPointFormat.finiteRoundTowardZero`
- `FloatingPointFormat.finiteRoundTowardNegative_eq_underflow`
- `FloatingPointFormat.finiteRoundTowardPositive_eq_underflow`
- `FloatingPointFormat.finiteRoundTowardZero_eq_underflow`
- `FloatingPointFormat.finiteRoundTowardNegative_eq_overflow_of_not_underflow`
- `FloatingPointFormat.finiteRoundTowardPositive_eq_overflow_of_not_underflow`
- `FloatingPointFormat.finiteRoundTowardZero_eq_overflow_of_not_underflow`
- `FloatingPointFormat.finiteRoundTowardNegative_le_of_finiteUnderflowRange`
- `FloatingPointFormat.le_finiteRoundTowardPositive_of_finiteUnderflowRange`
- `FloatingPointFormat.finiteRoundTowardZero_abs_le_abs_of_finiteUnderflowRange`
- `FloatingPointFormat.finiteRoundTowardNegative_le_of_finiteNormalRange`
- `FloatingPointFormat.le_finiteRoundTowardPositive_of_finiteNormalRange`
- `FloatingPointFormat.finiteRoundTowardZero_abs_le_abs_of_finiteNormalRange`
- `FloatingPointFormat.finiteRoundTowardZero_abs_le_abs`
- `FloatingPointFormat.finiteRoundToMode`
- `FloatingPointFormat.finiteRoundToMode_nearestEven`
- `FloatingPointFormat.finiteRoundToMode_towardZero`
- `FloatingPointFormat.finiteRoundToMode_towardPositive`
- `FloatingPointFormat.finiteRoundToMode_towardNegative`
- `FloatingPointFormat.finiteRoundToModeOp`
- `FloatingPointFormat.finiteRoundToModeOp_nearestEven`
- `FloatingPointFormat.finiteRoundToModeSqrt`
- `FloatingPointFormat.finiteRoundToModeSqrt_nearestEven`
- `FloatingPointFormat.finiteRoundToModeSqrt_ieeeUnderflowModeRoundingEvidence_of_finiteUnderflowRange`
- `FloatingPointFormat.sourceRoundToEvenEvidence`
- `FloatingPointFormat.sourceRoundToEvenEvidence_relErrorComputedDenom_le_unitRoundoff`
- `FloatingPointFormat.exists_nearestAdjacentRoundToEven_signedRelErrorWitness_lt_positive`
- `FloatingPointFormat.exists_nearestAdjacentRoundToEven_signedRelErrorWitness_lt_negative`
- `FloatingPointFormat.exists_finiteNormalRoundToEven_signedRelErrorWitness_lt_positive_finiteNormalRange`
- `FloatingPointFormat.exists_finiteNormalRoundToEven_signedRelErrorWitness_lt_negative_finiteNormalRange`
- `FloatingPointFormat.exists_finiteNormalRoundToEven_signedRelErrorWitness_lt_finiteNormalRange`
- `FloatingPointFormat.finiteNormalRoundToEven`
- `FloatingPointFormat.finiteNormalRoundToEven_spec`
- `FloatingPointFormat.finiteNormalRoundToEven_nearestRoundingToFinite`
- `FloatingPointFormat.finiteNormalRoundToEven_sourceRoundToEvenEvidence`
- `FloatingPointFormat.finiteNormalRoundToEven_signedRelErrorWitness_lt`
- `FloatingPointFormat.finiteNormalRoundToEven_inverseRelErrorModel`
- `FloatingPointFormat.finiteNormalRoundToEven_inverseRelErrorWitness`
- `FloatingPointFormat.nearestRoundingToUnbounded_abs_sub_le_half_adjacent_gap`
- `FloatingPointFormat.nearestRoundingToUnbounded_abs_sub_le_unitRoundoff_mul_anchor_of_realOrderAdjacent_between`
- `FloatingPointFormat.nearestRoundingToUnbounded_abs_sub_le_unitRoundoff_mul_self_of_nonneg_between`
- `FloatingPointFormat.nearestRoundingToUnbounded_abs_sub_le_unitRoundoff_mul_self_of_nonpos_between`
- `FloatingPointFormat.signedRelErrorWitness_of_abs_sub_le_unitRoundoff_mul_abs`
- `FloatingPointFormat.nearestRoundingToUnbounded_signedRelErrorWitness_of_nonneg_between`
- `FloatingPointFormat.nearestRoundingToUnbounded_signedRelErrorWitness_of_nonpos_between`
- `FloatingPointFormat.exists_nearestRoundingToUnbounded_signedRelErrorWitness_of_nonneg_between`
- `FloatingPointFormat.exists_nearestRoundingToUnbounded_signedRelErrorWitness_of_nonpos_between`
- `inverseRelErrorWitness`
- `inverseRelErrorModel`
- `inverseRelErrorWitness_iff_signedRelErrorWitness`
- `relErrorComputedDenom_eq_abs_inverse_factor`
- `inverseRelErrorModel_of_relErrorComputedDenom_le`
- `relErrorComputedDenom_le_of_inverseRelErrorModel`
- `inverseRelErrorModel_iff_relErrorComputedDenom_le`
- `inverseRelErrorModel_abs_exact_sub_computed_le`
- `FloatingPointFormat.exists_nearestRoundingToFinite_inverseRelErrorModel_finiteNormalRange`
- `FloatingPointFormat.exists_nearestRoundingToFinite_inverseRelErrorWitness_finiteNormalRange`
- `FloatingPointFormat.finiteNormalRange_ne_zero`
- `FloatingPointFormat.sourceRoundAwayEvidence`
- `FloatingPointFormat.sourceRoundAwayEvidence_relErrorComputedDenom_le_unitRoundoff`
- `FloatingPointFormat.exists_finiteNormalRoundAway_signedRelErrorWitness_lt_positive_finiteNormalRange`
- `FloatingPointFormat.exists_finiteNormalRoundAway_signedRelErrorWitness_lt_negative_finiteNormalRange`
- `FloatingPointFormat.exists_finiteNormalRoundAway_signedRelErrorWitness_lt_finiteNormalRange`
- `FloatingPointFormat.finiteNormalRoundAway`
- `FloatingPointFormat.finiteNormalRoundAway_spec`
- `FloatingPointFormat.finiteNormalRoundAway_nearestRoundingToFinite`
- `FloatingPointFormat.finiteNormalRoundAway_sourceRoundAwayEvidence`
- `FloatingPointFormat.finiteNormalRoundAway_signedRelErrorWitness_lt`
- `FloatingPointFormat.finiteNormalRoundAway_inverseRelErrorModel`
- `FloatingPointFormat.finiteNormalRoundAway_inverseRelErrorWitness`
- `FloatingPointFormat.finiteUnderflowRoundAwayNonneg`
- `FloatingPointFormat.finiteUnderflowRoundAwayNonneg_nearestRoundingToFinite`
- `FloatingPointFormat.finiteUnderflowRoundAway`
- `FloatingPointFormat.finiteUnderflowRoundAway_nearestRoundingToFinite`
- `FloatingPointFormat.finiteRoundAway`
- `FloatingPointFormat.finiteRoundAway_nearestRoundingToFinite`
- `FloatingPointFormat.finiteRoundAway_output_not_finiteOverflowRange`
- `FloatingPointFormat.finiteRoundAway_output_abs_le_maxFiniteMagnitude`
- `FloatingPointFormat.finiteRoundAway_sourceRoundAwayEvidence_of_finiteNormalRange`
- `FloatingPointFormat.finiteRoundAway_signedRelErrorWitness_lt_of_finiteNormalRange`
- `FloatingPointFormat.finiteRoundAway_inverseRelErrorModel_of_finiteNormalRange`
- `FloatingPointFormat.finiteRoundAway_inverseRelErrorWitness_of_finiteNormalRange`
- `FloatingPointFormat.finiteUnderflowRoundToEvenNonneg`
- `FloatingPointFormat.finiteUnderflowRoundToEvenNonneg_nearestRoundingToFinite`
- `FloatingPointFormat.finiteUnderflowRoundToEven`
- `FloatingPointFormat.finiteUnderflowRoundToEven_nearestRoundingToFinite`
- `FloatingPointFormat.finiteRoundToEven`
- `FloatingPointFormat.finiteRoundToEven_nearestRoundingToFinite`
- `FloatingPointFormat.finiteRoundToEven_output_not_finiteOverflowRange`
- `FloatingPointFormat.finiteRoundToEven_output_abs_le_maxFiniteMagnitude`
- `FloatingPointFormat.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange`
- `FloatingPointFormat.finiteRoundToEven_signedRelErrorWitness_lt_of_finiteNormalRange`
- `FloatingPointFormat.finiteRoundToEven_inverseRelErrorModel_of_finiteNormalRange`
- `FloatingPointFormat.finiteRoundToEven_inverseRelErrorWitness_of_finiteNormalRange`
- `FloatingPointFormat.nearestRoundingIn_eq_self_of_mem`
- `FloatingPointFormat.nearestRoundingToUnbounded_eq_self_of_mem`
- `FloatingPointFormat.nearestRoundingToFinite_eq_self_of_finiteSystem`
- `FloatingPointFormat.finiteRoundToEven_eq_self_of_finiteSystem`
- `FloatingPointFormat.finiteUnderflowRoundToEven_absError_le_gradualUnderflowEtaBound`
- `FloatingPointFormat.finiteUnderflowRoundToEven_absError_lt_gradualUnderflowEtaBound_of_noHalfTie`
- `FloatingPointFormat.finiteRoundToEven_absError_le_gradualUnderflowEtaBound_of_finiteUnderflowRange`
- `FloatingPointFormat.finiteRoundToEven_absError_lt_gradualUnderflowEtaBound_of_finiteUnderflowRange_of_noHalfTie`
- `FloatingPointFormat.finiteRoundToEven_additiveUnderflowModel_underflow_branch_of_finiteUnderflowRange`
- `FloatingPointFormat.finiteRoundToEven_strictAdditiveUnderflowModel_underflow_branch_of_finiteUnderflowRange_of_noHalfTie`
- `FloatingPointFormat.finiteRoundToEven_strictAdditiveUnderflowModel_normal_branch_of_finiteNormalRange`
- `FloatingPointFormat.finiteRoundToEvenOp`
- `FloatingPointFormat.finiteRoundToEvenOp_nearestRoundingToFinite`
- `FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem`
- `FloatingPointFormat.finiteRoundToEvenOp_add_zero_of_finiteSystem`
- `FloatingPointFormat.finiteRoundToEvenOp_signedRelErrorWitness_lt_of_finiteNormalRange`
- `FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange`
- `FloatingPointFormat.finiteRoundToEvenOp_inverseRelErrorWitness_of_finiteNormalRange`
- `FloatingPointFormat.finiteRoundToEvenOp_strictAdditiveUnderflowModel_normal_branch_of_finiteNormalRange`
- `FloatingPointFormat.finiteRoundToEvenOp_additiveUnderflowModel_underflow_branch_of_finiteUnderflowRange`
- `FloatingPointFormat.finiteRoundToEvenOp_strictAdditiveUnderflowModel_underflow_branch_of_finiteUnderflowRange_of_noHalfTie`
- `FloatingPointFormat.finiteRoundToEvenSqrt`
- `FloatingPointFormat.finiteRoundToEvenSqrt_nearestRoundingToFinite`
- `FloatingPointFormat.finiteRoundToEvenSqrt_eq_exact_of_finiteSystem`
- `FloatingPointFormat.finiteRoundToEvenSqrt_standardModel_lt_of_finiteNormalRange`
- `FloatingPointFormat.finiteRoundToEvenSqrt_inverseRelErrorWitness_of_finiteNormalRange`
- `FloatingPointFormat.finiteRoundToEvenSqrt_strictAdditiveUnderflowModel_normal_branch_of_finiteNormalRange`
- `FloatingPointFormat.finiteRoundToEvenSqrt_additiveUnderflowModel_underflow_branch_of_finiteUnderflowRange`
- `FloatingPointFormat.finiteRoundToEvenSqrt_strictAdditiveUnderflowModel_underflow_branch_of_finiteUnderflowRange_of_noHalfTie`
- `FloatingPointFormat.ieeeOverflowValue`
- `FloatingPointFormat.ieeeOverflowResult`
- `FloatingPointFormat.ieeeOverflowDefaultResult`
- `FloatingPointFormat.ieeeOverflowDefaultResult_value`
- `FloatingPointFormat.ieeeOverflowDefaultResult_hasFlag_iff`
- `FloatingPointFormat.ieeeOverflowDefaultResult_hasOverflowFlag`
- `FloatingPointFormat.ieeeOverflowDefaultResult_hasInexactFlag`
- `FloatingPointFormat.ieeeOverflowDefaultResult_ieeeOverflowResult_of_finiteOverflowRange`
- `FloatingPointFormat.ieeeOverflowValue_nearestEven_of_neg`
- `FloatingPointFormat.ieeeOverflowValue_nearestEven_of_nonneg`
- `FloatingPointFormat.ieeeOverflowValue_towardZero_of_neg`
- `FloatingPointFormat.ieeeOverflowValue_towardZero_of_nonneg`
- `FloatingPointFormat.ieeeOverflowValue_towardPositive_of_neg`
- `FloatingPointFormat.ieeeOverflowValue_towardPositive_of_nonneg`
- `FloatingPointFormat.ieeeOverflowValue_towardNegative_of_neg`
- `FloatingPointFormat.ieeeOverflowValue_towardNegative_of_nonneg`
- `FloatingPointFormat.ieeeOverflowResult_finiteOverflowRange`
- `FloatingPointFormat.ieeeOverflowResult_value`
- `FloatingPointFormat.ieeeOverflowResult_hasOverflowFlag`
- `FloatingPointFormat.ieeeOverflowResult_hasInexactFlag`
- `FloatingPointFormat.ieeeOverflowResult_not_noFlags`
- `FloatingPointFormat.ieeeOverflowResult_not_finiteNoFlags`
- `FloatingPointFormat.ieeeUnderflowResult`
- `FloatingPointFormat.ieeeUnderflowDefaultResult`
- `FloatingPointFormat.ieeeUnderflowDefaultResult_value`
- `FloatingPointFormat.ieeeUnderflowDefaultResult_toReal?`
- `FloatingPointFormat.ieeeUnderflowDefaultResult_hasFlag_iff`
- `FloatingPointFormat.ieeeUnderflowDefaultResult_hasUnderflowFlag`
- `FloatingPointFormat.ieeeUnderflowDefaultResult_hasInexactFlag_of_ne`
- `FloatingPointFormat.ieeeUnderflowDefaultResult_ieeeUnderflowResult`
- `FloatingPointFormat.ieeeUnderflowModeRoundingEvidence`
- `FloatingPointFormat.ieeeUnderflowModeResult`
- `FloatingPointFormat.ieeeUnderflowDefaultResult_ieeeUnderflowModeResult`
- `FloatingPointFormat.finiteOverflowSaturationIeeeFiniteResult`
- `FloatingPointFormat.finiteOverflowSaturationIeeeFiniteResult_isFinite`
- `FloatingPointFormat.finiteOverflowSaturationIeeeFiniteResult_noFlags`
- `FloatingPointFormat.finiteOverflowSaturationIeeeFiniteResult_not_ieeeOverflowResult`
- `FloatingPointFormat.finiteOverflowSaturationIeeeFiniteResult_toReal?`
- `FloatingPointFormat.finiteRoundToEvenIeeeFiniteResult`
- `FloatingPointFormat.finiteRoundToEvenIeeeFiniteResult_isFinite`
- `FloatingPointFormat.finiteRoundToEvenIeeeFiniteResult_noFlags`
- `FloatingPointFormat.finiteRoundToEvenIeeeFiniteResult_toReal?`
- `FloatingPointFormat.finiteRoundToEvenOpIeeeFiniteResult`
- `FloatingPointFormat.finiteRoundToEvenOpIeeeFiniteResult_isFinite`
- `FloatingPointFormat.finiteRoundToEvenOpIeeeFiniteResult_noFlags`
- `FloatingPointFormat.finiteRoundToEvenOpIeeeFiniteResult_toReal?`
- `FloatingPointFormat.ieeeRoundToNearestEvenOpResult`
- `FloatingPointFormat.ieeeRoundToNearestEvenOpResult_ieeeOverflowResult_of_finiteOverflowRange`
- `FloatingPointFormat.ieeeRoundToNearestEvenOpResult_noFlags_of_not_finiteOverflowRange_of_not_finiteUnderflowRange`
- `FloatingPointFormat.ieeeRoundToNearestEvenOpResult_toReal?_of_not_finiteOverflowRange`
- `FloatingPointFormat.ieeeRoundToNearestEvenOpResult_ieeeUnderflowResult_of_finiteUnderflowRange`
- `FloatingPointFormat.ieeeRoundToNearestEvenOpResult_ieeeUnderflowResult_and_additiveUnderflowModel`
- `FloatingPointFormat.ieeeRoundToModeOpResult`
- `FloatingPointFormat.ieeeRoundTowardZeroOpResult`
- `FloatingPointFormat.ieeeRoundTowardPositiveOpResult`
- `FloatingPointFormat.ieeeRoundTowardNegativeOpResult`
- `FloatingPointFormat.ieeeRoundToModeOpResult_nearestEven`
- `FloatingPointFormat.ieeeRoundToModeOpResult_ieeeOverflowResult_of_finiteOverflowRange`
- `FloatingPointFormat.ieeeRoundToModeOpResult_eq_finiteNoFlags_of_not_finiteOverflowRange_of_not_finiteUnderflowRange`
- `FloatingPointFormat.ieeeRoundToModeOpResult_noFlags_of_not_finiteOverflowRange_of_not_finiteUnderflowRange`
- `FloatingPointFormat.ieeeRoundToModeOpResult_toReal?_of_not_finiteOverflowRange`
- `FloatingPointFormat.finiteRoundToMode_ieeeUnderflowModeRoundingEvidence_of_finiteUnderflowRange`
- `FloatingPointFormat.finiteRoundToModeOp_ieeeUnderflowModeRoundingEvidence_of_finiteUnderflowRange`
- `FloatingPointFormat.ieeeRoundToModeOpResult_ieeeUnderflowModeResult_of_finiteUnderflowRange`
- `FloatingPointFormat.ieeeRoundTowardZeroOpResult_ieeeOverflowResult_of_finiteOverflowRange`
- `FloatingPointFormat.ieeeRoundTowardPositiveOpResult_ieeeOverflowResult_of_finiteOverflowRange`
- `FloatingPointFormat.ieeeRoundTowardNegativeOpResult_ieeeOverflowResult_of_finiteOverflowRange`
- `ieeeInvalidOperationResult`
- `ieeeInvalidOperationDefaultResult`
- `ieeeInvalidOperationDefaultResult_ieeeInvalidOperationResult`
- `ieeeInvalidOperationResult_not_finiteNoFlags`
- `ieeeDivisionByZeroInput`
- `ieeeDivisionByZeroResult`
- `ieeeDivisionByZeroDefaultResult`
- `ieeeDivisionByZeroSignedValue`
- `ieeeDivisionByZeroInput_finite_nonzero`
- `ieeeDivisionByZeroInput_finite_nonzero_posZero`
- `ieeeDivisionByZeroInput_finite_nonzero_negZero`
- `ieeeDivisionByZeroInput_finite_nonzero_finite_zero`
- `ieeeDivisionByZeroSignedValue_pos_over_posZero`
- `ieeeDivisionByZeroSignedValue_neg_over_posZero`
- `ieeeDivisionByZeroSignedValue_pos_over_negZero`
- `ieeeDivisionByZeroSignedValue_neg_over_negZero`
- `ieeeDivisionByZeroSignedValue_none_finite_zero`
- `ieeeDivisionByZeroFiniteZeroDefaultValue`
- `ieeeDivisionByZeroFiniteZeroDefaultValue_pos`
- `ieeeDivisionByZeroFiniteZeroDefaultValue_neg`
- `ieeeDivisionByZeroFiniteZeroDefaultValue_isInfinite`
- `ieeeDivisionByZeroDefaultResult_finite_zero`
- `ieeeDivisionByZeroDefaultResult_pos_over_finite_zero`
- `ieeeDivisionByZeroDefaultResult_neg_over_finite_zero`
- `ieeeDivisionByZeroDefaultResult_value`
- `ieeeDivisionByZeroDefaultResult_hasFlag_iff`
- `ieeeDivisionByZeroDefaultResult_hasDivisionByZeroFlag`
- `ieeeDivisionByZeroDefaultResult_ieeeDivisionByZeroResult`
- `ieeeDivisionByZeroDefaultResult_posInf_ieeeDivisionByZeroResult`
- `ieeeDivisionByZeroDefaultResult_negInf_ieeeDivisionByZeroResult`
- `ieeeDivisionByZeroDefaultResult_pos_over_posZero`
- `ieeeDivisionByZeroDefaultResult_neg_over_posZero`
- `ieeeDivisionByZeroDefaultResult_pos_over_negZero`
- `ieeeDivisionByZeroDefaultResult_neg_over_negZero`
- `ieeeDivisionByZeroResult_input`
- `ieeeDivisionByZeroResult_value_isInfinite`
- `ieeeDivisionByZeroResult_hasDivisionByZeroFlag`
- `ieeeDivisionByZeroResult_not_noFlags`
- `ieeeDivisionByZeroResult_not_finiteNoFlags`
- `IeeeValue.isNaN`
- `IeeeValue.isInfinite`
- `IeeeValue.isZero`
- `IeeeValue.sameSignedInfinities`
- `IeeeValue.oppositeSignedInfinities`
- `IeeeValue.ieeeUnordered`
- `IeeeValue.ieeeEq`
- `IeeeValue.ieeeLt`
- `IeeeValue.ieeeGt`
- `IeeeValue.ieeeUnordered_left_nan`
- `IeeeValue.ieeeUnordered_right_nan`
- `IeeeValue.ieeeUnordered_nan_self`
- `IeeeValue.not_ieeeEq_left_nan`
- `IeeeValue.not_ieeeEq_right_nan`
- `IeeeValue.not_ieeeEq_nan_self`
- `IeeeValue.not_ieeeEq_self_iff_isNaN`
- `IeeeValue.not_ieeeLt_left_nan`
- `IeeeValue.not_ieeeLt_right_nan`
- `IeeeValue.not_ieeeGt_left_nan`
- `IeeeValue.not_ieeeGt_right_nan`
- `IeeeValue.ieeeEq_posZero_negZero`
- `IeeeValue.ieeeEq_negZero_posZero`
- `IeeeValue.ieeeEq_self_of_not_isNaN`
- `IeeeValue.not_ieeeLt_self`
- `IeeeValue.not_ieeeGt_self`
- `IeeeValue.ieeeComparison_complete`
- `IeeeValue.ieeeComparison_ordered_of_not_unordered`
- `ieeeQuietNaNPropagationResult`
- `ieeeQuietNaNPropagationResult_left_nan`
- `ieeeQuietNaNPropagationResult_right_nan`
- `ieeeQuietNaNPropagationResult_value`
- `ieeeQuietNaNPropagationResult_noFlags`
- `ieeePrimitiveInvalidOperationInput`
- `ieeePrimitiveInvalidOperationResult`
- `ieeePrimitiveInvalidOperationInput_div_zero_zero`
- `ieeePrimitiveInvalidOperationInput_div_inf_inf`
- `ieeePrimitiveInvalidOperationInput_mul_zero_inf`
- `ieeePrimitiveInvalidOperationInput_mul_inf_zero`
- `ieeePrimitiveInvalidOperationInput_add_posInf_negInf`
- `ieeePrimitiveInvalidOperationInput_add_negInf_posInf`
- `ieeePrimitiveInvalidOperationInput_sub_posInf_posInf`
- `ieeePrimitiveInvalidOperationInput_sub_negInf_negInf`
- `ieeePrimitiveInvalidOperationDefaultResult_ieeePrimitiveInvalidOperationResult`
- `ieeePrimitiveInvalidOperationResult_value`
- `ieeePrimitiveInvalidOperationResult_hasInvalidOperationFlag`
- `ieeePrimitiveSpecialValueResult`
- `ieeePrimitiveSpecialValueResult_left_nan`
- `ieeePrimitiveSpecialValueResult_right_nan`
- `ieeePrimitiveSpecialValueResult_invalid_default`
- `ieeeSqrtInvalidResult`
- `ieeeSqrtInvalidDefaultResult`
- `ieeeSqrtInvalidDefaultResult_ieeeSqrtInvalidResult`
- `ieeeSqrtInvalidResult_hasInvalidOperationFlag`
- `ieeeSqrtSpecialValueResult`
- `ieeeSqrtSpecialValueResult_nan_valueNoFlags`
- `ieeeSqrtSpecialValueResult_posInf_valueNoFlags`
- `ieeeSqrtSpecialValueResult_negInf_invalid`
- `ieeeSqrtSpecialValueResult_value_nan`
- `ieeeSqrtSpecialValueResult_noFlags_nan`
- `ieeeSqrtSpecialValueResult_value_posInf`
- `ieeeSqrtSpecialValueResult_noFlags_posInf`
- `ieeeSqrtSpecialValueResult_negInf_ieeeInvalidOperationResult`
- `ieeeSqrtSignedZeroResult`
- `ieeeSqrtSignedZeroResult_posZero_valueNoFlags`
- `ieeeSqrtSignedZeroResult_negZero_valueNoFlags`
- `ieeeSqrtSignedZeroResult_value_posZero`
- `ieeeSqrtSignedZeroResult_noFlags_posZero`
- `ieeeSqrtSignedZeroResult_value_negZero`
- `ieeeSqrtSignedZeroResult_noFlags_negZero`
- `FloatingPointFormat.ieeeRoundToNearestEvenSqrtResult`
- `FloatingPointFormat.ieeeRoundToNearestEvenSqrtResult_ieeeSqrtInvalidResult_of_neg`
- `FloatingPointFormat.ieeeRoundToNearestEvenSqrtResult_ieeeInvalidOperationResult_of_neg`
- `FloatingPointFormat.ieeeRoundToNearestEvenSqrtResult_value_of_neg`
- `FloatingPointFormat.ieeeRoundToNearestEvenSqrtResult_hasInvalidOperationFlag_of_neg`
- `FloatingPointFormat.ieeeRoundToNearestEvenSqrtResult_toReal?_of_neg`
- `FloatingPointFormat.ieeeRoundToNearestEvenSqrtResult_ieeeOverflowResult_of_finiteOverflowRange`
- `FloatingPointFormat.ieeeRoundToNearestEvenSqrtResult_noFlags_of_not_finiteOverflowRange_of_not_finiteUnderflowRange`
- `FloatingPointFormat.ieeeRoundToNearestEvenSqrtResult_toReal?_of_not_finiteOverflowRange`
- `FloatingPointFormat.ieeeRoundToNearestEvenSqrtResult_ieeeUnderflowResult_of_finiteUnderflowRange`
- `FloatingPointFormat.ieeeRoundToNearestEvenSqrtResult_ieeeUnderflowResult_and_additiveUnderflowModel`
- `FloatingPointFormat.ieeeRoundToModeSqrtResult`
- `FloatingPointFormat.ieeeRoundTowardZeroSqrtResult`
- `FloatingPointFormat.ieeeRoundTowardPositiveSqrtResult`
- `FloatingPointFormat.ieeeRoundTowardNegativeSqrtResult`
- `FloatingPointFormat.ieeeRoundToModeSqrtResult_nearestEven`
- `FloatingPointFormat.ieeeRoundToModeSqrtResult_ieeeSqrtInvalidResult_of_neg`
- `FloatingPointFormat.ieeeRoundToModeSqrtResult_ieeeInvalidOperationResult_of_neg`
- `FloatingPointFormat.ieeeRoundToModeSqrtResult_value_of_neg`
- `FloatingPointFormat.ieeeRoundToModeSqrtResult_hasInvalidOperationFlag_of_neg`
- `FloatingPointFormat.ieeeRoundToModeSqrtResult_toReal?_of_neg`
- `FloatingPointFormat.ieeeRoundToModeSqrtResult_ieeeOverflowResult_of_finiteOverflowRange`
- `FloatingPointFormat.ieeeRoundToModeSqrtResult_eq_finiteNoFlags_of_not_finiteOverflowRange_of_not_finiteUnderflowRange`
- `FloatingPointFormat.ieeeRoundToModeSqrtResult_noFlags_of_not_finiteOverflowRange_of_not_finiteUnderflowRange`
- `FloatingPointFormat.ieeeRoundToModeSqrtResult_toReal?_of_not_finiteOverflowRange`
- `FloatingPointFormat.ieeeRoundToModeSqrtResult_ieeeUnderflowModeResult_of_finiteUnderflowRange`
- `FloatingPointFormat.ieeeRoundTowardZeroSqrtResult_ieeeOverflowResult_of_finiteOverflowRange`
- `FloatingPointFormat.ieeeRoundTowardPositiveSqrtResult_ieeeOverflowResult_of_finiteOverflowRange`
- `FloatingPointFormat.ieeeRoundTowardNegativeSqrtResult_ieeeOverflowResult_of_finiteOverflowRange`
- `FloatingPointFormat.ieeeRoundToNearestEvenSqrtValueResult`
- `FloatingPointFormat.ieeeRoundToNearestEvenSqrtValueResult_finite`
- `FloatingPointFormat.ieeeRoundToNearestEvenSqrtValueResult_nan_special`
- `FloatingPointFormat.ieeeRoundToNearestEvenSqrtValueResult_posZero_signedZero`
- `FloatingPointFormat.ieeeRoundToNearestEvenSqrtValueResult_negZero_signedZero`
- `FloatingPointFormat.ieeeRoundToNearestEvenSqrtValueResult_posInf_special`
- `FloatingPointFormat.ieeeRoundToNearestEvenSqrtValueResult_negInf_special`
- `FloatingPointFormat.ieeeRoundToNearestEvenSqrtValueResult_nan_value`
- `FloatingPointFormat.ieeeRoundToNearestEvenSqrtValueResult_nan_noFlags`
- `FloatingPointFormat.ieeeRoundToNearestEvenSqrtValueResult_posZero_value`
- `FloatingPointFormat.ieeeRoundToNearestEvenSqrtValueResult_posZero_noFlags`
- `FloatingPointFormat.ieeeRoundToNearestEvenSqrtValueResult_posZero_toReal?`
- `FloatingPointFormat.ieeeRoundToNearestEvenSqrtValueResult_negZero_value`
- `FloatingPointFormat.ieeeRoundToNearestEvenSqrtValueResult_negZero_noFlags`
- `FloatingPointFormat.ieeeRoundToNearestEvenSqrtValueResult_negZero_toReal?`
- `FloatingPointFormat.ieeeRoundToNearestEvenSqrtValueResult_posInf_value`
- `FloatingPointFormat.ieeeRoundToNearestEvenSqrtValueResult_posInf_noFlags`
- `FloatingPointFormat.ieeeRoundToNearestEvenSqrtValueResult_negInf_ieeeInvalidOperationResult`
- `FloatingPointFormat.ieeeRoundToNearestEvenSqrtValueResult_negInf_value`
- `FloatingPointFormat.ieeeRoundToNearestEvenSqrtValueResult_negInf_hasInvalidOperationFlag`
- `FloatingPointFormat.finiteRoundToEvenSqrtIeeeFiniteResult`
- `FloatingPointFormat.finiteRoundToEvenSqrtIeeeFiniteResult_isFinite`
- `FloatingPointFormat.finiteRoundToEvenSqrtIeeeFiniteResult_noFlags`
- `FloatingPointFormat.finiteRoundToEvenSqrtIeeeFiniteResult_toReal?`
- `FloatingPointFormat.finiteNormalFl`
- `FloatingPointFormat.finiteNormalFl_spec`
- `FloatingPointFormat.finiteNormalFl_nearestRoundingToFinite`
- `FloatingPointFormat.finiteNormalFl_inverseRelErrorModel`
- `FloatingPointFormat.finiteNormalFl_inverseRelErrorWitness`
- `FloatingPointFormat.finiteNormalFl_signedRelErrorWitness`
- `FloatingPointFormat.machineEpsilon_pos`
- `FloatingPointFormat.unitRoundoff_pos`
- `FloatingPointFormat.signedRelErrorWitness_of_abs_sub_lt_unitRoundoff_mul_abs`
- `FloatingPointFormat.nearestRoundingToUnbounded_abs_sub_lt_unitRoundoff_mul_self_of_nonneg_between`
- `FloatingPointFormat.nearestRoundingToUnbounded_abs_sub_lt_unitRoundoff_mul_self_of_nonpos_between`
- `FloatingPointFormat.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_nonzero`
- `FloatingPointFormat.exists_nearestRoundingToFinite_signedRelErrorWitness_lt_finiteNormalRange`
- `FloatingPointFormat.nearestRoundingToFinite_signedRelErrorWitness_lt_of_finiteNormalRange`
- `FloatingPointFormat.finiteNormalFl_signedRelErrorWitness_lt`

Scope of closure: the finite-format definitions now encode Higham's source
parameters `beta`, `t`, `emin`, `emax`; normalized and subnormal mantissas;
inclusive exponent range; normalized and subnormal value forms; finite and
unbounded representable sets; structural and real-order adjacency predicates;
and nearest-rounding relations.  The closed
lemmas prove basic nonzero/in-range sanity checks, base positivity, absolute
normalization of (2.1), per-exponent bounds
`beta^(e-1) <= |y| < beta^e`, the exact smallest/largest normalized endpoint
values, the global finite-normalized range
`beta^(emin-1) <= |y| <= beta^emax * (1 - beta^(-t))`, the subnormal absolute
value form, the strict bound below the smallest normal, the smallest positive
subnormal value when a subnormal mantissa exists, equal subnormal successor
spacing `beta^(emin-t)`, the boundary spacing from the largest subnormal
mantissa to the smallest normal, same-exponent successor spacing `beta^(e-t)`,
exponent-boundary spacing between the largest mantissa at
exponent `e` and the smallest mantissa at exponent `e+1`, the positional
digit-string representation (2.2), fixed-length digit-string reconstruction
for every mantissa in range, normalized digit-string reconstruction for every
normalized mantissa, and uniqueness of fixed-length digit strings with the same
encoded mantissa, full uniqueness of signed normalized `(m,e)` representations
as real values, the structural
adjacency version of the Lemma 2.1 relative-spacing bounds with respect to the
left endpoint, endpoint membership/distinctness facts for structural adjacent
pairs, cross-exponent/all-sign no-between facts for same-exponent structural
successors, exponent-boundary no-between facts, the theorem that every
structural adjacent normalized pair is `realOrderAdjacentNormalized`, the
same-sign classification for real-order adjacent normalized representations,
the positive ordered exponent classification to same-or-successor exponent,
the positive ordered same-exponent mantissa-successor classification, the
positive ordered exponent-boundary endpoint classification, the positive
ordered and unordered real-order-to-structural adjacency theorems, the
negative-representation reduction to the positive case, structural and
real-order adjacency symmetry, the converse from arbitrary real-order
adjacency to structural adjacency, the real-order Lemma 2.1 relative-spacing
theorem, exact self-rounding for representable normalized/finite inputs, the
δ = 0 signed relative-error witness for already normalized inputs, the
finite-system zero membership/rounding facts, the finite exact-input
`delta = 0` signed witness, the source-facing finite zero signed witness, the
nearest-rounding endpoint-selection/existence theorem for a point bracketed by
adjacent normalized values, the half-gap theorem, positive/negative
adjacent-bracket relative-error bounds with respect to unit roundoff,
positive/negative adjacent-bracket signed relative-error witnesses, the
floor-based natural mantissa bracketing lemma, the same-exponent signed
fixed-bin bracketing theorems that either identify an exact normalized mantissa
or supply adjacent normalized endpoints, the same-exponent positive/negative
nearest-rounding signed-witness theorems, the positive endpoint equalities
`normalizedValue_false_minNormalMantissa_eq` and
`normalizedValue_false_maxNormalMantissa_eq`, the source-shaped power-interval
signed-witness adapters, the source-shaped exponent-boundary signed-witness
adapters, the source-facing finite normal/underflow/overflow range predicates
`minNormalMagnitude`, `maxFiniteMagnitude`, `finiteNormalRange`,
`finiteUnderflowRange`, and `finiteOverflowRange`, the classification that
normalized values lie in finite normal range while subnormals lie in the
underflow range, the proofs that the positive/negative smallest-normal and
largest-finite endpoints are normalized finite values, the theorem that
finite-system values are never in the overflow range, the corresponding finite
nearest-rounding output
classification/non-overflow/magnitude-bound wrappers, the relation-level
positive/negative overflow-range saturation theorems to the signed largest
finite endpoints, the smallest-subnormal magnitude/lower-bound facts, the
finite zero nearest-rounding theorem at half the smallest subnormal magnitude,
the strict tiny-input theorem that every finite nearest-rounded value is zero,
the positive/negative normal-range bridge that turns a finite output of the
unbounded nearest-rounding relation into a finite nearest-rounding relation,
the strict adjacent-bracket and strict finite-normal-range signed-witness
theorems for Higham Theorem 2.2, and the displayed
`u = (1/2) beta^(1-t)` relationship.
The inverse-model theorems close the algebraic/computed-denominator form of
Higham Chapter 2 equation (2.5): `computed = exact / (1 + delta)` is
equivalent, under nonzero exact/computed values, to a computed-denominator
relative-error bound, and implies the Chapter 3 running-error bound shape
`|exact - computed| <= u * |computed|`.  The new computed-denominator rounding
lemmas now combine this algebra with the finite-normal-range nearest-rounding
relation to prove the relation-valued finite-normal-range version of Theorem
2.3.  The same finite-normal arbitrary choice `finiteNormalFl` now also carries
the strict forward witness for Theorem 2.2.  The local selector
`nearestAdjacentRoundAway` chooses the nearer endpoint in a supplied adjacent
bracket and breaks exact distance ties toward the endpoint of larger magnitude,
with strict signed-witness wrappers for nonnegative and nonpositive brackets;
`nearestAdjacentRoundToEven` chooses the nearer endpoint in the same local
adjacent-bracket setting and breaks exact ties using the supplied left
mantissa's parity, with Lean theorems for the left/right closer cases, exact
tie branches, and nearest-rounding validity for real-order and same-exponent
adjacent brackets.  The local directed selectors now fix exact endpoints and
otherwise choose the lower endpoint for toward-negative, the upper endpoint for
toward-positive, and the sign-dependent endpoint toward zero, with
representability and one-sided/order facts for nonnegative and nonpositive
adjacent brackets.  The finite-normal directed source selectors lift those
local choices through exponent-slice evidence and prove unbounded-normalized
representability, `y <= x` for toward-negative, `x <= y` for toward-positive,
and `|y| <= |x|` for toward-zero.  Same-exponent/source
power-interval/power-slice wrappers
expose either exact self-rounding or the local round-away value.
`finiteNormalRoundAway` is now a
proof-carrying finite-normal source choice whose nearest finite output carries
that round-away evidence, Higham's strict signed witness, and the inverse
relative-error witness.  `finiteNormalRoundToEven` is now the matching
finite-normal source choice for the local round-to-even policy: exact
representable inputs return themselves, non-exact brackets record the left
endpoint's normalized mantissa for the tie rule, and the selected finite output
carries Higham's strict signed witness and the inverse relative-error witness.
`finiteUnderflowRoundAway` and `finiteUnderflowRoundToEven` now supply
matching source-facing underflow branches on the subnormal lattice, choosing
larger magnitude for round-away ties and lower-index parity for round-to-even
ties.  `finiteRoundAway` and `finiteRoundToEven` combine their underflow
branches with the finite-normal selectors and overflow saturation, prove
nearest-rounding validity for every real input, recover the strict forward
and inverse witnesses on finite-normal inputs, and fix finite representable
inputs exactly.  The local adjacent-bracket directed selectors now provide
exact endpoint-preserving choices and one-sided/order facts, and the
finite-normal directed selectors lift those facts through normal-range source
evidence.  `finiteUnderflowRoundTowardZero`,
`finiteUnderflowRoundTowardPositive`, and
`finiteUnderflowRoundTowardNegative` add subnormal-lattice underflow branches,
and `finiteRoundTowardNegative`, `finiteRoundTowardPositive`, and
`finiteRoundTowardZero` combine underflow, finite-normal, and finite-saturation
overflow branches as total source-facing finite directed selectors.  The
finite mode selector `finiteRoundToMode` packages nearest/even and the three
directed finite policies; the primitive-operation and square-root IEEE wrappers
now dispatch finite underflow/no-flag branches through the corresponding mode
selectors.  The remaining operation-level gap is full concrete IEEE semantics
with traps, signaling-NaN/payload behavior, full concrete comparison instructions beyond the predicate layer, and broad special
values beyond the first primitive/square-root/comparison predicate branches.
`finiteRoundToEvenOp` and `finiteRoundToEvenSqrt` now provide
the ordinary finite, non-exceptional operation-level bridge from exact real
primitive operations and square root to the strict standard-model equation
whenever the exact result is finite-normal, and to exact self-rounding whenever
the exact result is finite representable.  `finiteRoundToEvenOp_add_zero_of_finiteSystem`
closes the finite left-add-zero side condition for this wrapper.
The IEEE-facing vocabulary now separates finite values from infinities/NaNs,
records rounding modes and exception flags, and embeds the current
source-facing finite selectors only as finite, flag-free operation results.
This still does not prove finite-format arithmetic with underflow/IEEE
exception behavior or an explicit concrete IEEE operation integrating all
special-value/tie-breaking branches.

## Already Covered Before This Audit

| Source item | Local Lean status |
|---|---|
| Standard model (2.4), lines 234--244 | `FPModel`, `FPModel.model_basicOp`; non-strict formal variant `|delta| <= u`; division has nonzero denominator side condition. |
| No-guard model (2.6), lines 411--450 | `noGuardAddWitness`, `noGuardSubWitness`, `noGuardMulDivWitness`, `noGuardBasicOpWitness`, and `NoGuardFPModel`; add/sub use separate strict perturbations on the two input terms, while mul/div use strict relative-error witnesses. |
| Guard-digit theorem surface, lines 466--495 | `FloatingPointFormat.normalizedExponentRepresentation`, `FloatingPointFormat.fergusonExponentCondition`, `FloatingPointFormat.normalizedExponentRepresentation_sub_exponent_gap_le_one`, `FloatingPointFormat.normalizedValue_sub_fergusonCondition_sign_eq`, `FloatingPointFormat.fergusonExponentCondition_exponent_gap_le_one`, `FloatingPointFormat.fergusonExponentCondition_same_sign_and_exponent_gap`, `FloatingPointFormat.fergusonExponentCondition_same_sign_exponent_cases`, `FloatingPointFormat.alignedSameExponentSubtractionValue`, `FloatingPointFormat.sameExponentMantissaDiffInt`, `FloatingPointFormat.sameExponentMantissaDiffInt_cast`, `FloatingPointFormat.sameExponentMantissaDiffInt_natAbs_lt_mantissaBound`, `FloatingPointFormat.minNormalMantissa_mul_beta_eq_mantissaBound`, `FloatingPointFormat.sameExponentRenormalizationWitness`, `FloatingPointFormat.sameExponentSubnormalEndpointWitness`, `FloatingPointFormat.sameExponent_shift_search`, `FloatingPointFormat.scaledIntegerValue_finiteSystem_of_natAbs_lt_mantissaBound`, `FloatingPointFormat.sameExponentFiniteDifferenceWitness`, `FloatingPointFormat.sameExponentFiniteDifferenceWitness_of_normalizedMantissas`, `FloatingPointFormat.guardDigitTailMantissa_eq_natAbs_of_natAbs_lt_mantissaBound`, `FloatingPointFormat.guardDigitRoundedCoeff_eq_self_of_natAbs_lt_mantissaBound`, `FloatingPointFormat.guardDigitRoundedSameExponentSubtractionValue`, `FloatingPointFormat.normalizedValue_sub_sameSign_sameExponent_eq_guardDigitRounded`, `FloatingPointFormat.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_natAbs_eq_zero`, `FloatingPointFormat.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_normalizedDiff`, `FloatingPointFormat.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_beta_mul_normalizedDiff`, `FloatingPointFormat.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_beta_pow_mul_normalizedDiff`, `FloatingPointFormat.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_renormalizationWitness`, `FloatingPointFormat.normalizedValue_sub_sameSign_sameExponent_finiteSystem_at_emin_of_natAbs_lt_minNormalMantissa`, `FloatingPointFormat.normalizedValue_sub_sameSign_sameExponent_finiteSystem_at_shifted_emin_of_natAbs_mul_beta_pow_lt_minNormalMantissa`, `FloatingPointFormat.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_subnormalEndpointWitness`, `FloatingPointFormat.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_finiteDifferenceWitness`, `FloatingPointFormat.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_normalizedMantissas`, `FloatingPointFormat.sameExponentSubnormalEndpointWitness_of_emin_natAbs_lt_minNormalMantissa`, `FloatingPointFormat.sameExponentFiniteDifferenceWitness_of_emin_natAbs_lt_minNormalMantissa`, `FloatingPointFormat.guardAlignedMantissaDiff`, `FloatingPointFormat.guardAlignedMantissaDiffInt`, `FloatingPointFormat.guardAlignedMantissaDiffInt_cast`, `FloatingPointFormat.alignedAdjacentExponentSubtractionValue`, `FloatingPointFormat.alignedAdjacentExponentSubtractionValue_finiteSystem_of_natAbs_lt_mantissaBound`, `FloatingPointFormat.normalizedValue_sub_sameSign_adjacentExponent_finiteSystem_of_natAbs_lt_mantissaBound`, `FloatingPointFormat.guardAlignedMantissaDiff_abs_lt_minNormalMantissa_of_fergusonAdjacent`, `FloatingPointFormat.guardAlignedMantissaDiffInt_abs_lt_minNormalMantissa_of_fergusonAdjacent`, `FloatingPointFormat.guardAlignedMantissaDiffInt_natAbs_lt_minNormalMantissa_of_fergusonAdjacent`, `FloatingPointFormat.guardAlignedMantissaDiffInt_pos_of_adjacentNormalizedMantissas`, `FloatingPointFormat.guardAlignedMantissaDiffInt_natAbs_lt_mantissaBound_of_sterbenzAdjacent`, `FloatingPointFormat.normalizedValue_sub_positive_adjacentExponent_finiteSystem_of_sterbenzAdjacent`, `FloatingPointFormat.sterbenzRatioCondition_positive_normalized_exponent_gap_le_one`, `FloatingPointFormat.normalizedValue_sub_positive_finiteSystem_of_sterbenzRatioCondition`, `FloatingPointFormat.normalizedSystem_sub_finiteSystem_of_sterbenzRatioCondition`, `FloatingPointFormat.subnormalValue_false_pos`, `FloatingPointFormat.subnormalValue_true_neg`, `FloatingPointFormat.subnormalValue_sub_sameSign_finiteSystem_of_subnormalMantissas`, `FloatingPointFormat.subnormalSystem_sub_finiteSystem_of_sterbenzRatioCondition`, `FloatingPointFormat.normalizedValue_sub_subnormalValue_positive_finiteSystem_of_sterbenzRatioCondition`, `FloatingPointFormat.normalizedSystem_sub_subnormalSystem_finiteSystem_of_sterbenzRatioCondition`, `FloatingPointFormat.subnormalSystem_sub_normalizedSystem_finiteSystem_of_sterbenzRatioCondition`, `FloatingPointFormat.finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition`, `FloatingPointFormat.guardDigitLeadingDigit`, `FloatingPointFormat.guardDigitTailMantissa`, `FloatingPointFormat.guardDigitRoundedCoeff`, `FloatingPointFormat.guardDigitRoundedAdjacentExponentSubtractionValue`, `FloatingPointFormat.guardDigitLeadingDigit_eq_zero_of_fergusonAdjacent`, `FloatingPointFormat.guardDigitTailMantissa_eq_natAbs_of_fergusonAdjacent`, `FloatingPointFormat.guardDigitRoundedCoeff_eq_self_of_fergusonAdjacent`, `FloatingPointFormat.normalizedValue_sub_sameSign_adjacentExponent_eq_guardDigitRounded_of_fergusonAdjacent`, `FloatingPointFormat.guardAlignedMantissaDiffInt_natAbs_lt_minNormalMantissa_of_fergusonAdjacent_reversed`, `FloatingPointFormat.normalizedValue_sub_sameSign_reversedAdjacentExponent_eq_neg_guardDigitRounded_of_fergusonAdjacent`, `FloatingPointFormat.guardDigitRoundedBranchSubtractionValue`, `FloatingPointFormat.guardDigitRoundedBranchSubtractionValue_eq_sub_of_ferguson`, `FloatingPointFormat.guardDigitBranchSubtractionModel`, `FloatingPointFormat.guardDigitBranchSubtractionModel_guardDigitSubtractionModel`, `FloatingPointFormat.guardDigitBranchSubtractionModel_exact_of_fergusonCondition`, `FloatingPointFormat.GuardDigitBranchSubtractionData`, `FloatingPointFormat.GuardDigitBranchSubtractionData.exponent_cases`, `FloatingPointFormat.GuardDigitBranchSubtractionData.branchValue_eq_sub`, `FloatingPointFormat.guardDigitRoundedBranchSubtractionValue_finiteSystem_of_ferguson`, `FloatingPointFormat.GuardDigitBranchSubtractionData.branchValue_finiteSystem`, `FloatingPointFormat.guardDigitBranchSubtractionRoutine`, `FloatingPointFormat.guardDigitBranchSubtractionRoutine_eq_sub_of_data`, `FloatingPointFormat.guardDigitBranchSubtractionRoutine_branchModel`, `FloatingPointFormat.guardDigitBranchSubtractionRoutine_guardDigitSubtractionModel`, `FloatingPointFormat.guardDigitBranchSubtractionRoutine_exact_of_fergusonCondition`, `FloatingPointFormat.guardDigitBranchSubtractionRoutine_finiteSystem_of_data`, `FloatingPointFormat.guardDigitBranchSubtractionRoutine_finiteSystem_of_fergusonCondition`, `FloatingPointFormat.guardDigitSubtractionModel`, `FloatingPointFormat.finiteRoundToEvenOp_sub_sameSign_sameExponent_eq_exact`, `FloatingPointFormat.finiteRoundToEvenOp_sub_positive_adjacentExponent_eq_exact_of_sterbenzAdjacent`, `FloatingPointFormat.finiteRoundToEvenOp_sub_positive_eq_exact_of_sterbenzRatioCondition`, `FloatingPointFormat.finiteRoundToEvenOp_sub_normalizedSystem_eq_exact_of_sterbenzRatioCondition`, `FloatingPointFormat.finiteRoundToEvenOp_sub_sameSign_subnormal_eq_exact`, `FloatingPointFormat.finiteRoundToEvenOp_sub_subnormalSystem_eq_exact_of_sterbenzRatioCondition`, `FloatingPointFormat.finiteRoundToEvenOp_sub_normalizedSystem_subnormalSystem_eq_exact_of_sterbenzRatioCondition`, `FloatingPointFormat.finiteRoundToEvenOp_sub_subnormalSystem_normalizedSystem_eq_exact_of_sterbenzRatioCondition`, `FloatingPointFormat.finiteRoundToEvenOp_sub_finiteSystem_eq_exact_of_sterbenzRatioCondition`, `FloatingPointFormat.finiteRoundToEvenOp_sub_eq_exact_of_guardDigitBranchSubtractionData`, `FloatingPointFormat.finiteRoundToEvenOp_sub_eq_exact_of_fergusonCondition`, `FloatingPointFormat.sterbenzRatioCondition_symm`, `FloatingPointFormat.sterbenzRatioCondition_abs_sub_lt_min`, `FloatingPointFormat.decimalSingleDigitFormat_sterbenzRatio_not_ferguson`, and `FloatingPointFormat.sterbenzFergusonBridgeCondition`; exactness follows under the explicit Ferguson condition, the source proof's exponent-gap, same-sign, and case-split reductions are proved, the raw aligned subtraction identities are formalized, the same-exponent rounded-coefficient branch is exact, the same-exponent exact difference is finite normalized when the exact integer mantissa difference is already normalized, the one-base-shift and arbitrary finite radix-power shift same-exponent exact differences are finite normalized when the shifted integer difference is normalized and the shifted exponent is in range, exact zero is finite, the same-exponent exact difference is finite at `emin` when that integer difference is below the normalized leading-digit threshold, and the shifted `emin` subnormal endpoint is finite when a finite radix-power shift lands below that threshold; the one-shift guard coefficient, including its integer `beta*mHigh - mLow` form, is bounded below the normalized leading-digit threshold in both adjacent orientations, the direct positive Sterbenz adjacent-exponent branch proves this coefficient is positive and below the `t`-digit mantissa bound under the ratio condition, the generic bounded-integer adapter turns this into finite-system and exact finite round-to-even positive adjacent-exponent subtraction, and the symmetric ratio plus one-exponent-gap lemmas lift the same-exponent/adjacent case split to positive normalized Sterbenz finite-system and exact finite round-to-even subtraction, the normalized-system wrapper lifts that representation-level result to source-shaped normalized operands, the subnormal sign and same-sign subnormal lattice theorems close all-subnormal Sterbenz finite-system and exact finite round-to-even subtraction, and the mixed normal/subnormal lattice theorem closes the source-facing finite-system all-case Sterbenz theorem, the proof sentence `z1 = 0` is formalized for the `t+1` guard word, dropping that zero guard digit is proved to preserve the adjacent-exponent exact value, the branch model is proved to satisfy `guardDigitSubtractionModel`, the noncomputable evidence-selecting `guardDigitBranchSubtractionRoutine` is exact and finite under Ferguson's condition, the branch-selected value is finite with the same-exponent branch discharged by the derived selector, concrete finite round-to-even subtraction is exact for same-exponent normalized operands, positive normalized, all-subnormal, mixed normal/subnormal, and all finite Sterbenz operands, and Ferguson branch data, and a decimal counterexample rules out deriving Ferguson's exponent condition from Sterbenz's ratio condition in general bases, while a fully executable digit-level/full IEEE implementation and corresponding full IEEE operation theorem remain open. |
| Square-root standard-model note, line 244 | `FPModel.model_sqrt`, for nonnegative real inputs. |
| Unit roundoff as an abstract model parameter, lines 157--158 and 242 | `FPModel.u`, `FPModel.u_nonneg`; no concrete IEEE value is derived. |
| Finite-format vocabulary, lines 49--78 and 143--159 | `FloatingPointFormat` and its normalized/subnormal/finite/unbounded/nearest-rounding predicates.  Per-exponent normalized range, exact finite normalized endpoint formulas, global finite-normalized magnitude bounds, source-facing finite normal/underflow/overflow range predicates, positional digit strings and their equivalence/uniqueness as integer mantissas, cross-exponent same-sign ordering, same-exponent successor-spacing, exponent-boundary spacing, structural normalized-adjacency foundations, structural endpoint facts, all-sign no-between facts, structural-to-real-order adjacency, the converse from arbitrary real-order adjacency back to structural adjacency, the real-order Lemma 2.1 relative-spacing theorem, relation-based finite zero rounding, finite-system output range/non-overflow/magnitude classification for the nearest-rounding relation, finite underflow output classifiers separating zero from subnormal values, the relation-valued signed subnormal nearest grid, relation-level finite-underflow existence, the total arbitrary finite nearest choice `finiteNearestFl`, the source-facing total finite round-away selector `finiteRoundAway`, the source-facing total finite round-to-even selector `finiteRoundToEven`, relation-level and source-facing signed overflow saturation to largest-finite endpoints via `finiteOverflowSaturation`, positive/negative normal-range finite-output bridges, the non-strict and strict finite-normal-range relation versions of Theorem 2.2, the arbitrary finite-nearest-output versions `nearestRoundingToFinite_signedRelErrorWitness_of_finiteNormalRange` and `nearestRoundingToFinite_signedRelErrorWitness_lt_of_finiteNormalRange`, the source-style finite-normal choice theorem `finiteNormalFl_signedRelErrorWitness_lt`, the finite-normal round-away source choices `finiteNormalRoundAway_signedRelErrorWitness_lt` and `finiteNormalRoundAway_inverseRelErrorWitness`, the finite-normal round-to-even source choices `finiteNormalRoundToEven_signedRelErrorWitness_lt` and `finiteNormalRoundToEven_inverseRelErrorWitness`, the finite-normal directed source choices `finiteNormalRoundTowardNegative`, `finiteNormalRoundTowardPositive`, and `finiteNormalRoundTowardZero`, the finite underflow directed choices `finiteUnderflowRoundTowardZero`, `finiteUnderflowRoundTowardPositive`, and `finiteUnderflowRoundTowardNegative`, the total finite directed source choices `finiteRoundTowardNegative`, `finiteRoundTowardPositive`, and `finiteRoundTowardZero`, the finite mode selector `finiteRoundToMode`, the total finite round-away normal-range witnesses `finiteRoundAway_signedRelErrorWitness_lt_of_finiteNormalRange` and `finiteRoundAway_inverseRelErrorWitness_of_finiteNormalRange`, the total finite round-to-even normal-range witnesses `finiteRoundToEven_signedRelErrorWitness_lt_of_finiteNormalRange` and `finiteRoundToEven_inverseRelErrorWitness_of_finiteNormalRange`, the relation-valued finite-normal-range inverse version of Theorem 2.3, global nonzero unbounded-normalized nearest-rounding signed-witness/computed-denominator existence, global nonzero/finite-normal/total finite round-away and round-to-even selector evidence, local adjacent directed endpoint selectors with representability and one-sided/order facts, finite flag-free IEEE-facing wrappers for the current source-facing finite selectors, the first flagged IEEE overflow/underflow/invalid-operation default-result constructors, division-by-zero infinite-result predicates, signed-zero denominator value-selection lemmas, and ordinary finite-zero denominator default lemmas, signed-zero value vocabulary and signed-zero comparison equality, modeled NaN unordered/unequal comparison predicates and predicate-level comparison completeness, primitive-operation plus square-root invalid/overflow/underflow dispatches, mode-parameterized primitive-operation and square-root overflow/underflow/no-flags dispatches and directed overflow aliases, primitive quiet-NaN/invalid-operation special-value predicates, square-root NaN/positive-infinity/negative-infinity special-value branches, and square-root signed-zero preservation are now proved.  This still does not prove operational IEEE traps, remaining infinity/special-value propagation beyond the first primitive/square-root/comparison predicate branches, signaling-NaN/payload behavior, full concrete comparison instruction semantics beyond the predicate layer, or concrete IEEE operations. |
| Computed-denominator relative-error algebra, related to Theorem 2.3/(2.5) | Chapter 1 `relErrorComputedDenom` API existed; this audit added the source-facing inverse-model bridge and now connects it to finite-normal-range nearest rounding by `FloatingPointFormat.exists_nearestRoundingToFinite_inverseRelErrorWitness_finiteNormalRange`. |

## Line-By-Line Source Ledger

| Lines | Source content | Status |
|---:|---|---|
| 1--47 | Chapter title and epigraphs. | Prose only; no Lean theorem obligation. |
| 49--78 | Definition of the floating-point number system `F`, equation (2.1), parameters `beta`, `t`, `emin`, `emax`, normalized mantissa, range, and positional form (2.2). | Closed for the normalized integer-mantissa and positional-digit surfaces used by the finite-format model.  `FloatingPointFormat` models the parameters, normalized mantissa, exponent range, and value expression (2.1), proves the per-exponent range `beta^(e-1) <= |y| < beta^e`, proves endpoint membership for the smallest/largest normalized values, proves `|minNormal * beta^(emin-t)| = beta^(emin-1)`, proves the exact largest normalized endpoint `beta^emax * (1 - beta^(-t))`, proves the global finite-normalized magnitude bound `beta^(emin-1) <= |y| <= beta^emax * (1 - beta^(-t))`, formalizes the positional digit form (2.2) as big-endian fixed-length digit strings via `positionalMantissa`/`positionalValue`, reconstructs canonical digit strings for integer mantissas, proves uniqueness of fixed-length digit strings, and proves signed normalized `(m,e)` representation uniqueness by `normalizedValue_eq_iff_sign_exp_mantissa`. |
| 55--62, 169--174 | Handwritten Greek annotations in the PDF extraction. | Treated as non-source annotation, not as a Higham theorem obligation. |
| 79--115 | Unequal spacing example for `beta=2`, `t=3`, machine epsilon, spacing discussion. | Closed as reusable normalized-spacing infrastructure.  `normalizedValue_succ_spacing` proves same-exponent successor spacing is `beta^(e-t)`, `normalizedValue_boundary_spacing` proves the exponent-boundary successor spacing, `realOrderAdjacentNormalized` states the ordered-set target, `realOrderAdjacentNormalized_of_adjacentNormalized` proves structural adjacent pairs are adjacent in the ordered normalized set, and `adjacentNormalized_of_realOrderAdjacentNormalized` proves the converse classification. |
| 116--120 | Lemma 2.1: adjacent normalized spacing is between `beta^{-1} eps_M |x|` and `eps_M |x|`, away from zero. | Closed for arbitrary real-order adjacent normalized endpoints.  `realOrderAdjacentNormalized_spacing_bounds_left` proves the displayed left-endpoint inequalities after classifying real-order adjacency into the structural same-exponent and exponent-boundary cases. |
| 121--139 | Subnormal/denormalized numbers, smallest positive normalized number, smallest positive subnormal number, equal spacing near zero. | Partly closed.  `minSubnormalMagnitude` names `beta^(emin-t)`, `subnormalValue_abs` proves the absolute-value form for `+- m beta^(emin-t)`, `subnormalValue_abs_lt_min_normal` proves every subnormal lies below the smallest normalized magnitude, `subnormalValue_one_abs_eq`/`subnormalValue_false_one_eq` identify the unit-mantissa subnormal value, `one_subnormalMantissa_of_subnormalMantissa` records that mantissa `1` is valid whenever any positive subnormal mantissa exists, `subnormalValue_false_one_le_of_subnormalMantissa` proves it is the least positive subnormal value in that case, `subnormalValue_succ_spacing` proves equal spacing between consecutive subnormal mantissas, `subnormalValue_boundary_spacing` proves the same spacing to the smallest positive normal, and `finiteSystem_ne_zero_abs_ge_minSubnormalMagnitude` proves every nonzero finite value has magnitude at least the smallest subnormal.  Open: full gradual-underflow semantics, IEEE underflow/exception behavior, and signed-zero/infinity/NaN behavior. |
| 143--159 | Infinite exponent set `G`, nearest rounding map `fl`, tie-breaking, overflow/underflow definitions, unit roundoff `u = (1/2) beta^(1-t)`. | Partly closed.  The finite/unbounded systems, finite normal/underflow/overflow ranges, machine epsilon/unit roundoff, exact self-rounding, finite zero rounding, finite output range/non-overflow/magnitude classifiers, underflow zero/subnormal classifiers, signed subnormal nearest grid, overflow saturation, finite-normal relation theorems for Theorems 2.2 and 2.3, arbitrary total nearest choice `finiteNearestFl`, source-facing finite round-away selector `finiteRoundAway`, local adjacent-bracket round-to-even tie selector `nearestAdjacentRoundToEven`, local adjacent-bracket directed selectors, finite-normal directed source selectors, finite-underflow directed selectors, total finite directed selectors, finite-normal source-facing round-to-even selector `finiteNormalRoundToEven`, finite-underflow round-to-even selector `finiteUnderflowRoundToEven`, and total finite round-to-even selector `finiteRoundToEven` are now proved.  The source-facing round-away selector uses `finiteUnderflowRoundAway` in the underflow band, `finiteNormalRoundAway` in the finite-normal band, and `finiteOverflowSaturation` in the overflow band; it is nearest for every real input and satisfies the strict forward and inverse witnesses on finite-normal inputs.  The total finite directed selectors use subnormal-lattice underflow branches, finite-normal directed branches, and finite overflow saturation; toward-zero has the global finite-selector theorem `finiteRoundTowardZero_abs_le_abs`.  The source-facing round-to-even selector uses `finiteUnderflowRoundToEven` in the underflow band, `finiteNormalRoundToEven` in the finite-normal band, and `finiteOverflowSaturation` in the overflow band; it is nearest for every real input and satisfies the strict forward and inverse witnesses on finite-normal inputs.  The IEEE primitive-operation and square-root mode wrappers now dispatch finite underflow/no-flag branches through `finiteRoundToModeOp`/`finiteRoundToModeSqrt`, and the IEEE special-value/comparison layer has first primitive quiet-NaN and invalid-operation predicates plus modeled NaN unordered/unequal, signed-zero equality, and predicate-level comparison-completeness predicates. Open: signed-zero/infinity/NaN behavior beyond the first primitive/square-root/comparison predicate branches, traps, full gradual-underflow/IEEE exception behavior, and concrete IEEE operation semantics. |
| 161--180 | Theorem 2.2: finite-format nearest rounding gives `fl(x)=x(1+delta)`, `|delta|<u`. | Closed for finite-normal-range nearest rounding, for the total source-facing round-away selector on finite-normal inputs, for the finite-normal source-facing round-to-even selector, and for the total source-facing round-to-even selector on finite-normal inputs.  `exists_nearestRoundingToFinite_signedRelErrorWitness_lt_finiteNormalRange` proves the relation theorem, `nearestRoundingToFinite_signedRelErrorWitness_lt_of_finiteNormalRange` proves the same strict witness for any finite nearest-rounded output, `finiteNormalFl_signedRelErrorWitness_lt` proves it for the arbitrary finite-normal choice, `finiteRoundAway_signedRelErrorWitness_lt_of_finiteNormalRange` proves it for the total source-facing finite round-away wrapper on finite-normal inputs, `finiteNormalRoundToEven_signedRelErrorWitness_lt` proves it for the finite-normal round-to-even selector, and `finiteRoundToEven_signedRelErrorWitness_lt_of_finiteNormalRange` proves it for the total source-facing finite round-to-even wrapper on finite-normal inputs.  The underflow/overflow branches of `finiteRoundAway` and `finiteRoundToEven` are nearest-rounded, but Theorem 2.2's relative-error statement remains a finite-normal-range theorem.  Local `FPModel` still assumes a non-strict primitive-operation model and does not derive arithmetic from this finite-format selector. Open: operation-level finite underflow/IEEE exception behavior, directed rounding, IEEE special values, and deriving arithmetic from concrete IEEE operations. |
| 181--191 | Theorem 2.3: inverse representation `fl(x)=x/(1+delta)`, `|delta|<=u`. | Closed for finite-normal-range relation-valued nearest rounding, the arbitrary source choice `finiteNormalFl`, the finite-normal round-away selector `finiteNormalRoundAway`, the finite-normal round-to-even selector `finiteNormalRoundToEven`, the total source-facing finite round-away wrapper `finiteRoundAway` restricted to finite-normal inputs, and the total source-facing finite round-to-even wrapper `finiteRoundToEven` restricted to finite-normal inputs.  The algebraic inverse-model/computed-denominator bridge is closed by `inverseRelErrorModel_iff_relErrorComputedDenom_le`; the adjacent-bracket computed-denominator bound is closed by `nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_of_realOrderAdjacent_between`; `exists_nearestRoundingToFinite_inverseRelErrorWitness_finiteNormalRange`, `finiteNormalFl_inverseRelErrorWitness`, `finiteNormalRoundAway_inverseRelErrorWitness`, `finiteNormalRoundToEven_inverseRelErrorWitness`, `finiteRoundAway_inverseRelErrorWitness_of_finiteNormalRange`, and `finiteRoundToEven_inverseRelErrorWitness_of_finiteNormalRange` provide the theorem surfaces.  Open: concrete IEEE derivation and operation-level special-value/exception semantics. |
| 193--229 | IEEE single/double parameter values, wobbling precision, ulp definition, MATLAB/Fortran epsilon note. | Partly closed.  `ieeeSingleFormat` records `beta = 2`, `t = 24`, `emin = -125`, `emax = 128`, with `ieeeSingleFormat_machineEpsilon` proving `eps_M = 2^(-23)`, `ieeeSingleFormat_unitRoundoff` proving `u = 2^(-24)`, and `ieeeSingleFormat_ulpAtExponent` proving `ulp(e) = 2^(e-24)`.  `ieeeDoubleFormat` records `beta = 2`, `t = 53`, `emin = -1021`, `emax = 1024`, with `ieeeDoubleFormat_machineEpsilon` proving `eps_M = 2^(-52)`, `ieeeDoubleFormat_unitRoundoff` proving `u = 2^(-53)`, and `ieeeDoubleFormat_ulpAtExponent` proving `ulp(e) = 2^(e-53)`.  The generic `ulpAtExponent` API names Higham's `beta^(e-t)` formula, `normalizedValue_wobblingPrecision_bounds` proves the ulp scale lies between `beta^(-1) eps_M * abs(x)` and `eps_M * abs(x)`, `realOrderAdjacentNormalized_relativeSpacing_bounds_left` proves the relative-distance wobbling interval for adjacent normalized endpoints, and `ieeeSingleFormat_realOrderAdjacentNormalized_relativeSpacing_bounds_left` specializes Figure 2.1's IEEE single numerical bounds to `2^(-24)` through `2^(-23)`.  `matlabIeeeDoubleEps` records MATLAB's IEEE-double `eps` convention as machine epsilon, `matlabIeeeDoubleEps_eq_two_zpow_neg52` proves it is `2^(-52)`, `matlabIeeeDoubleEps_eq_two_mul_ieeeDoubleFormat_unitRoundoff` makes explicit that it is twice the unit roundoff, and `fortranEpsilon` records the Fortran `EPSILON` convention for a real kind as machine epsilon.  The IEEE result layer now uses the displayed rounding-mode names for default overflow results, finite directed source selectors exist, and the primitive-operation and square-root mode wrappers use finite mode selectors for underflow/no-flag branches.  Open: Figure 2.1 as a plotted graphic artifact and full IEEE semantics. |
| 234--260 | Model of arithmetic, standard model (2.4), square-root note, model limitations, modified model (2.5). | Partly closed.  (2.4) and square root are modeled abstractly by `FPModel`; (2.5)'s algebraic surface is closed by this audit.  `finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange` and `finiteRoundToEvenSqrt_standardModel_lt_of_finiteNormalRange` now derive the strict standard-model equation for the ordinary finite, non-exceptional real-valued operation wrappers when the exact result is finite-normal.  `finiteRoundToEvenOp_eq_exact_of_finiteSystem`, `finiteRoundToEvenOp_sub_sameSign_sameExponent_eq_exact`, `finiteRoundToEvenOp_sub_positive_adjacentExponent_eq_exact_of_sterbenzAdjacent`, `finiteRoundToEvenOp_sub_positive_eq_exact_of_sterbenzRatioCondition`, `finiteRoundToEvenOp_sub_normalizedSystem_eq_exact_of_sterbenzRatioCondition`, `finiteRoundToEvenOp_sub_sameSign_subnormal_eq_exact`, `finiteRoundToEvenOp_sub_subnormalSystem_eq_exact_of_sterbenzRatioCondition`, `finiteRoundToEvenOp_sub_normalizedSystem_subnormalSystem_eq_exact_of_sterbenzRatioCondition`, `finiteRoundToEvenOp_sub_subnormalSystem_normalizedSystem_eq_exact_of_sterbenzRatioCondition`, `finiteRoundToEvenOp_sub_finiteSystem_eq_exact_of_sterbenzRatioCondition`, `finiteRoundToEvenOp_sub_eq_exact_of_guardDigitBranchSubtractionData`, `finiteRoundToEvenOp_sub_eq_exact_of_fergusonCondition`, `finiteRoundToEvenSqrt_eq_exact_of_finiteSystem`, and `finiteRoundToEvenOp_add_zero_of_finiteSystem` close exact finite representable operation/square-root results and the finite left-add-zero side condition for this wrapper.  `ieeeRoundToNearestEvenOpResult_*` and `ieeeRoundToModeOpResult_*` give the first IEEE-facing primitive-operation overflow/underflow/no-flags result dispatches, with mode-dependent overflow values and mode-specific primitive finite branches through `finiteRoundToModeOp`; `ieeeRoundToModeSqrtResult_*` adds mode-specific square-root finite branches through `finiteRoundToModeSqrt`.  `ieeeRoundToNearestEvenSqrtResult_ieeeOverflowResult_of_finiteOverflowRange`, `ieeeRoundToNearestEvenSqrtResult_ieeeUnderflowResult_of_finiteUnderflowRange`, and `ieeeRoundToNearestEvenSqrtResult_ieeeUnderflowResult_and_additiveUnderflowModel` give the first IEEE-facing real square-root overflow/underflow branches for nonnegative inputs; `ieeeRoundToNearestEvenSqrtResult_ieeeSqrtInvalidResult_of_neg` gives the negative-input invalid-operation/NaN branch.  A total `FPModel` instance over all real inputs and derivation from full IEEE rounding remain open. |
| 263--268 | Note on using standard model unless stated; weaker no-guard model (2.6). | Closed at the abstract model layer.  `noGuardAddWitness` and `noGuardSubWitness` formalize (2.6a)'s separate strict operand perturbations for addition/subtraction, `noGuardMulDivWitness` formalizes (2.6b)'s strict relative-error branch for multiplication/division, `noGuardBasicOpWitness` unifies the four primitive cases, and `NoGuardFPModel.model_basicOp` packages them as an abstract no-guard arithmetic model. |
| 270--409 | IEEE 754 overview, formats, exceptions, rounding modes, NaN, signed zeros, infinities, subnormals, extended precision, double rounding, IEEE 854. | Partly formalized at the vocabulary and first overflow/underflow/invalid-operation/division-by-zero/special-value/comparison result layer.  `IeeeRoundingMode`, `IeeeExceptionFlag`, `IeeeValue`, and `IeeeOperationResult` name the finite/signed-zero/infinite/NaN result space, rounding-mode space, and exception-flag space.  `IeeeValue.posZero`, `IeeeValue.negZero`, `ieeeSqrtSignedZeroResult`, and `ieeeRoundToNearestEvenSqrtValueResult_*Zero_*` record the first signed-zero operation branch: square root preserves positive and negative zero with no flags.  `IeeeValue.ieeeUnordered`, `IeeeValue.ieeeEq`, `IeeeValue.ieeeLt`, and `IeeeValue.ieeeGt` record the modeled comparison layer, including NaN unordered/unequal facts, the `x != x` NaN test, and positive-zero/negative-zero equality.  `ieeeOverflowValue` records the mode-dependent overflow value, `ieeeOverflowResult` requires source-facing overflow-range input plus overflow/inexact flags, and `ieeeOverflowDefaultResult_ieeeOverflowResult_of_finiteOverflowRange` constructs that default overflow result.  `ieeeUnderflowResult` records finite nearest-rounded underflow results with an underflow flag and conditional inexact flag; `ieeeUnderflowModeRoundingEvidence` and `ieeeUnderflowModeResult` add the corresponding mode-aware underflow evidence for nearest/even nearest rounding and directed finite one-sided/toward-zero branches.  `ieeeInvalidOperationResult`, `ieeeInvalidOperationDefaultResult`, `ieeeSqrtInvalidResult`, and `ieeeSqrtInvalidDefaultResult` record the NaN/invalid-operation branch for square root of negative real inputs.  `ieeeDivisionByZeroInput`, `ieeeDivisionByZeroResult`, `ieeeDivisionByZeroDefaultResult`, `ieeeDivisionByZeroSignedValue`, and `ieeeDivisionByZeroFiniteZeroDefaultValue` record the Table 2.2 finite-nonzero-over-zero case as an infinite result with the division-by-zero flag; signed `+0`/`-0` denominators select `+Inf` or `-Inf` according to numerator and denominator signs; the ordinary modeled `finite 0` denominator has a separate signless default selector for positive and negative finite numerators.  `ieeeQuietNaNPropagationResult`, `ieeePrimitiveInvalidOperationInput`, `ieeePrimitiveInvalidOperationResult`, and `ieeePrimitiveSpecialValueResult` add the first primitive-operation special-value predicates: quiet NaN propagation with no flags and invalid-operation/NaN results for `0/0`, `0 * infinity`, `infinity * 0`, `infinity / infinity`, and indeterminate infinity addition/subtraction.  `ieeeSqrtSpecialValueResult` and `ieeeRoundToNearestEvenSqrtValueResult` record the first square-root special-value branches: NaN propagates to NaN with no flags, positive infinity returns positive infinity with no flags, and negative infinity returns invalid-operation/NaN.  `ieeeRoundToNearestEvenOpResult_ieeeOverflowResult_of_finiteOverflowRange` and `ieeeRoundToNearestEvenOpResult_ieeeUnderflowResult_of_finiteUnderflowRange` dispatch nearest/even primitive-operation overflow/underflow exact results to those flagged IEEE-facing results.  `ieeeRoundToModeOpResult` generalizes the primitive-operation result wrapper over `IeeeRoundingMode`; `ieeeRoundToModeOpResult_ieeeOverflowResult_of_finiteOverflowRange` and the three directed alias overflow theorems prove that overflow uses the mode-dependent `ieeeOverflowValue` table for nearest/even, toward-zero, toward-positive, and toward-negative modes, while `ieeeRoundToModeOpResult_ieeeUnderflowModeResult_of_finiteUnderflowRange` and the no-flag theorem prove that primitive finite underflow/no-flag branches dispatch through `finiteRoundToModeOp`.  `ieeeRoundToModeSqrtResult` adds mode-aware square-root overflow/underflow/no-flag branches through `finiteRoundToModeSqrt`, and `ieeeRoundToNearestEvenSqrtResult_ieeeSqrtInvalidResult_of_neg`, `ieeeRoundToNearestEvenSqrtResult_ieeeOverflowResult_of_finiteOverflowRange`, and `ieeeRoundToNearestEvenSqrtResult_ieeeUnderflowResult_of_finiteUnderflowRange` cover finite-real negative, overflow, and underflow square-root branches.  `IeeeOperationResult.finiteNoFlags` and the `finite*IeeeFiniteResult` wrappers embed the current finite real-valued saturation/round-to-even/op/sqrt policies only as finite, flag-free results, with `finiteOverflowSaturationIeeeFiniteResult_not_ieeeOverflowResult` preventing finite saturation from being used as IEEE overflow semantics.  `binaryDoubleRounding_counterexample` closes the finite-format existence claim that extended-precision rounding followed by destination rounding can differ from direct destination rounding.  `problem2_9_direct_double_rounds_to_predecessor`, `problem2_9_direct_double_sqrt_rounds_to_predecessor`, `problem2_9_extended64_rounds_to_double_midpoint`, `problem2_9_double_rounds_extended_midpoint_to_one`, and `problem2_9_double_rounding_from_extended64` close Problem 2.9 at the finite-selector layer: direct finite double square-root rounding gives `1 - 2^-53`, whereas rounding first to a local 64-bit-mantissa extended format gives `1 - 2^-54` and then final double rounding gives `1`.  Open: full concrete IEEE operations, traps, signaling-NaN/payload behavior, full concrete comparison instruction semantics beyond the predicate layer, remaining special-value propagation beyond these first primitive/square-root/comparison predicate branches, and full directed operation semantics beyond primitive/square-root finite branches. |
| 411--464 | Aberrant arithmetics, guard-digit example, no-guard model (2.6a,b). | Partly closed.  The no-guard model (2.6a,b) is now formalized abstractly by `NoGuardFPModel`; `NoGuardFPModel.model_add_error_eq` and `NoGuardFPModel.model_sub_error_eq` expose the add/sub error splits `x*alpha + y*beta` and `x*alpha - y*beta`, while `NoGuardFPModel.model_mul_signedRelErrorWitness` and `NoGuardFPModel.model_div_signedRelErrorWitness` retain strict relative-error witnesses for `*` and `/`.  The displayed base-two, three-mantissa-digit example is recorded by `noGuardBinaryT3_exact_difference`, `noGuardBinaryT3_truncated_difference`, `noGuardBinaryT3_truncated_factor_two`, and `noGuardBinaryT3_truncated_relError_eq_one`.  Open: a concrete guard-digit subtraction algorithm, Cray-family operation models, and the remaining Ferguson/Sterbenz executable/full-case exact-subtraction theorems. |
| 466--495 | Theorem 2.4 (Ferguson) and Theorem 2.5 (Sterbenz). | The theorem surface and noncomputable evidence-selecting branch routine are now explicit, but the fully executable digit-level theorem is still open.  `normalizedExponentRepresentation` models the exponent-bearing normalized representation used by `e(x)`, `fergusonExponentCondition` packages the source condition `e(x-y) < min(e(x), e(y))` together with normalized finite representations of `x`, `y`, and `x-y`, and `guardDigitSubtractionModel_exact_of_fergusonCondition` proves exactness for any subtraction routine satisfying that guard-digit model.  `fergusonExponentCondition_sub_not_finiteUnderflowRange` and `fergusonExponentCondition_sub_not_finiteOverflowRange` expose the finite-format side condition on `x-y`; `normalizedExponentRepresentation_sub_exponent_gap_le_one` and `fergusonExponentCondition_exponent_gap_le_one` prove the proof-text reduction that the exponents of `x` and `y` differ by at most one; `normalizedValue_sub_fergusonCondition_sign_eq`, `fergusonExponentCondition_same_sign_and_exponent_gap`, and `fergusonExponentCondition_same_sign_exponent_cases` prove the next proof-text reductions that the remaining branches use same-sign operands and are exactly the same-exponent or one-exponent-shift cases.  `alignedSameExponentSubtractionValue` and `normalizedValue_sub_sameSign_sameExponent_eq_aligned` formalize the same-exponent aligned mantissa subtraction identity; `sameExponentMantissaDiffInt_cast` connects its integer coefficient with the real mantissa difference; `sameExponentMantissaDiffInt_natAbs_lt_mantissaBound` proves that same-exponent subtraction has at most `t` digits; `guardDigitRoundedCoeff_eq_self_of_natAbs_lt_mantissaBound`, `guardDigitRoundedSameExponentSubtractionValue`, and `normalizedValue_sub_sameSign_sameExponent_eq_guardDigitRounded` prove that the modeled `t`-digit coefficient rounding preserves that same-exponent subtraction value; `normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_normalizedDiff` proves that this exact same-exponent result is finite normalized when the exact integer mantissa difference is already normalized; `normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_beta_mul_normalizedDiff` proves the one-base-shift same-exponent result is finite normalized at exponent `e - 1` when that shifted integer difference is normalized and `e - 1` is in range; `normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_beta_pow_mul_normalizedDiff` proves the arbitrary finite radix-power shift branch under the corresponding shifted-normalized-mantissa and shifted-exponent hypotheses; and `normalizedValue_sub_sameSign_sameExponent_finiteSystem_at_emin_of_natAbs_lt_minNormalMantissa` proves that the exact same-exponent result is finite at `emin` when that integer difference is below the normalized leading-digit threshold, and `normalizedValue_sub_sameSign_sameExponent_finiteSystem_at_shifted_emin_of_natAbs_mul_beta_pow_lt_minNormalMantissa` proves the shifted `emin` subnormal endpoint.  `guardAlignedMantissaDiff`, `guardAlignedMantissaDiffInt`, `guardAlignedMantissaDiffInt_cast`, `alignedAdjacentExponentSubtractionValue`, and `normalizedValue_sub_sameSign_adjacentExponent_eq_aligned` formalize the one-exponent-shift guard-aligned raw difference `beta*mHigh - mLow` and its integer coefficient; `alignedAdjacentExponentSubtractionValue_abs`, `guardAlignedMantissaDiff_abs_lt_minNormalMantissa_of_fergusonAdjacent`, `guardAlignedMantissaDiffInt_abs_lt_minNormalMantissa_of_fergusonAdjacent`, and `guardAlignedMantissaDiffInt_natAbs_lt_minNormalMantissa_of_fergusonAdjacent` prove that Ferguson's `e(x-y) < e(y)` side condition forces that guard-aligned coefficient below the normalized leading-digit threshold in real, integer, and natural absolute-value forms; the reversed-orientation variants prove the same coefficient bound and exact negated rounded adjacent value when the lower-exponent operand is subtracted first.  `guardDigitLeadingDigit_eq_zero_of_fergusonAdjacent` and `guardDigitTailMantissa_eq_natAbs_of_fergusonAdjacent` formalize the source proof sentence that the leading digit `z1` of the `t+1` guard word is zero and the trailing `t`-digit tail is unchanged; `guardDigitRoundedBranchSubtractionValue_eq_sub_of_ferguson`, `guardDigitBranchSubtractionModel_guardDigitSubtractionModel`, and `guardDigitBranchSubtractionModel_exact_of_fergusonCondition` package the same-exponent, high-minus-low adjacent, and low-minus-high adjacent cases into a branch implementation contract satisfying the guard-digit model.  `GuardDigitBranchSubtractionData` packages the representation-selection evidence for the branch selector, `GuardDigitBranchSubtractionData.branchValue_eq_sub` proves such data select the exact branch value, and `guardDigitBranchSubtractionRoutine_branchModel`, `guardDigitBranchSubtractionRoutine_guardDigitSubtractionModel`, and `guardDigitBranchSubtractionRoutine_exact_of_fergusonCondition` prove the noncomputable branch routine satisfies the guard model and is exact under Ferguson's condition.  `sterbenzRatioCondition` records `y/2 < x < 2*y`; `sterbenzRatioCondition_y_pos` and `sterbenzRatioCondition_x_pos` prove the implied positivity; `sterbenzRatioCondition_abs_sub_lt_left`, `sterbenzRatioCondition_abs_sub_lt_right`, and `sterbenzRatioCondition_abs_sub_lt_min` prove the ratio-distance inequalities; `guardAlignedMantissaDiffInt_natAbs_lt_mantissaBound_of_sterbenzAdjacent`, `normalizedValue_sub_positive_adjacentExponent_finiteSystem_of_sterbenzAdjacent`, and `finiteRoundToEvenOp_sub_positive_adjacentExponent_eq_exact_of_sterbenzAdjacent` close the positive adjacent-exponent Sterbenz branch; `sterbenzRatioCondition_symm`, `sterbenzRatioCondition_positive_normalized_exponent_gap_le_one`, `normalizedValue_sub_positive_finiteSystem_of_sterbenzRatioCondition`, `normalizedSystem_sub_finiteSystem_of_sterbenzRatioCondition`, `subnormalSystem_sub_finiteSystem_of_sterbenzRatioCondition`, `normalizedValue_sub_subnormalValue_positive_finiteSystem_of_sterbenzRatioCondition`, `normalizedSystem_sub_subnormalSystem_finiteSystem_of_sterbenzRatioCondition`, `subnormalSystem_sub_normalizedSystem_finiteSystem_of_sterbenzRatioCondition`, `finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition`, `finiteRoundToEvenOp_sub_positive_eq_exact_of_sterbenzRatioCondition`, `finiteRoundToEvenOp_sub_normalizedSystem_eq_exact_of_sterbenzRatioCondition`, and `finiteRoundToEvenOp_sub_subnormalSystem_eq_exact_of_sterbenzRatioCondition`, `finiteRoundToEvenOp_sub_normalizedSystem_subnormalSystem_eq_exact_of_sterbenzRatioCondition`, `finiteRoundToEvenOp_sub_subnormalSystem_normalizedSystem_eq_exact_of_sterbenzRatioCondition`, and `finiteRoundToEvenOp_sub_finiteSystem_eq_exact_of_sterbenzRatioCondition` lift that branch with the same-exponent and subnormal-lattice cases to positive normalized and all-subnormal Sterbenz finite-system and finite-rounding exactness; `guardDigitSubtractionModel_exact_of_sterbenzBridge` proves exactness under the current explicit bridge condition; and `decimalSingleDigitFormat_sterbenzRatio_not_ferguson` proves that Sterbenz's ratio condition does not imply Ferguson's exponent condition in general bases.  Open: formalize a fully executable digit-level/full IEEE subtraction implementation and derive the corresponding full IEEE operation theorem. |
| 496--521 | Heron's formula instability and Kahan reordered formula (2.7). | Closed for the modeled finite round-to-even/no-underflow trace with explicit finite-normal-range hypotheses.  `Heron.lean` names the exact Heron/Kahan expressions and rounded operation trace, proves the exact product identity, ordered-side positivity, all exact Kahan factor-positivity lemmas, and the squared-area identity, derives exact finite round-to-even computation of the sensitive `a-b` subtraction from Sterbenz, packages strict finite-normal-range witnesses for every remaining rounded operation in `finiteKahanHeronTrace_standardModel_lt_of_finiteNormalRange`, and proves exact expanded radicand/area equations.  The final stability layer is now closed by `kahanHeronExpandedRadicand_eq_exact_mul_local_factors`, `kahanHeronRadicandLocalErrors_abs_le_unitRoundoff`, `kahanHeronTraceStandardModel_radicand_rel_error_le_gamma9`, `kahanHeronTraceStandardModel_area_eq_kahanArea_mul_sqrt_gamma9`, `kahanHeronTraceStandardModel_area_relError_le_gamma9_unitRoundoff`, and the direct theorem `finiteKahanHeronArea_relError_le_gamma9_unitRoundoff_of_finiteNormalRange`, giving relative error at most `(1 + gamma 9) * (1 + u)^2 - 1`.  Full IEEE exception/underflow/special-value semantics remain tracked under the general C2.19--C2.20 IEEE rows, not as a C2.14 gap. |
| 523--577 | Choice of base, wobbling precision, Brent/logarithmic distribution, Benford leading-digit distribution, examples. | Partly closed.  `LeadingDigitDistribution.lean` formalizes the displayed logarithmic leading-digit law: `logarithmicLeadingDigitMass` names the mass of digit `n`, `logarithmicLeadingDigitMass_eq_log_div` exposes the equivalent form `log_beta ((n+1)/n)`, `logarithmicLeadingDigitMass_eq_log_one_add_inv` exposes the source form `log_beta (1+1/n)`, `logarithmicLeadingDigitMass_nonneg` proves each digit mass is nonnegative for bases `beta > 1`, `logarithmicLeadingDigitMass_succ_lt` proves adjacent masses strictly decrease with the digit, `sum_logarithmicLeadingDigitMass_eq_one` proves the masses over leading digits `1, ..., beta-1` telescope to `1`, and `logarithmicLeadingDigitProbability` packages the law as a finite probability distribution on `Fin (beta-1)`.  `decimalLogarithmicLeadingDigitProbability_prob_eq` and `decimalLogarithmicLeadingDigitProbability_prob_eq_log_one_add_inv` specialize the decimal table shape to digits `1` through `9`, while `decimalLogarithmicLeadingDigitProbability_first_gt_last` and `decimalLogarithmicLeadingDigitProbability_nonuniform` formalize the source observation that decimal leading digits are not equally likely.  `logarithmicIntervalMass_mul_base_pow`, `logarithmicIntervalMass_mul_base_zpow`, `logarithmicLeadingDigitMass_scaled_bin`, and `logarithmicLeadingDigitMass_scaled_bin_zpow` prove the algebraic scale-invariance surface for positive bins multiplied by natural or integer powers of the base.  Open: Brent's base-2 optimality theorem for worst-case/mean-square representation error, the stronger scale-invariance-equivalence theorem, product-convergence-to-logarithmic distribution, the `q^k` equidistribution/Gelfand claim, and empirical matrix-table claims. |
| 579--631 | Statistical distribution of rounding errors, rule of thumb replacing `n` by `sqrt n`, random rounding/PRECISE/CESTAC discussion. | Partly closed.  `StatisticalRounding.lean` formalizes the finite-probability second-moment core behind the displayed rule of thumb.  `StatisticalRoundingErrorModel` records visible assumptions that rounding errors are zero-mean, pairwise uncorrelated, and have per-step second moment at most `u^2`; `expectation_sum_eq_zero` proves the accumulated error has mean zero; `expectation_sum_sq_eq_sum_second_moments` proves the cross terms vanish; `expectation_sum_sq_le_card_mul_unit_sq` bounds the accumulated second moment by `n*u^2`; and `rms_sum_le_sqrt_card_mul_unit` proves the RMS accumulated error is at most `sqrt n * u`.  This closes the finite variance/square-root theorem under explicit statistical assumptions.  Open: deriving those assumptions from a concrete random-rounding scheme, CLT/asymptotic normality, PRECISE/CESTAC formal models, logarithmic-mantissa rounding-error distributions, and the text's descriptive/historical claims. |
| 633--690 | Alternative number systems, especially level-index arithmetic. | Partly closed.  `AlternativeNumberSystems.lean` formalizes the concrete level-index representation described in the text.  `levelIndexForward` decodes a level/fraction pair by applying `exp` `level` times; `levelIndexBackward` applies `log` `level` times; `levelIndexBackward_forward` proves that the iterated logarithm recovers the fractional index; `LevelIndexCode` records a code with `f in [0,1]`; `LevelIndexCode.index` records the displayed scalar code `l+f`; `LevelIndexCode.value` and `LevelIndexCode.reciprocalValue` model the positive-side and reciprocal-side decoders; and `LevelIndexCode.reciprocalValue_mul_value_of_pos_level` proves the reciprocal branch is inverse to the positive-side value for positive levels.  Open/descriptive: larger/smaller range comparisons, addition/subtraction cost claims, controversy/comparative-advantage statements, and the other cited alternative systems. |
| 692--774 | Accuracy tests, Tables 2.3--2.5, sine/power/guard-digit tests. | Partly closed.  `AccuracyTests.lean` records the exact real-arithmetic baselines behind the displayed tests.  `unitRoundoffProbeExact_eq_zero` proves the Table 2.3 unit-roundoff probe is zero in exact arithmetic; `codySineTestExact` names the sine target, `codySineTestExact_eq_neg_sin_reducedArgument` proves the exact argument-reduction identity `sin(22) = -sin(22-7*pi)`, `codySineTestExact_neg` plus `codySineTestExact_abs_lt_one_hundredth` certify the source-facing sign and coarse magnitude bound, `sineTaylorOdd5_abs_error_le_next`, `codySineReducedArgument_sineTaylorOdd5_abs_error_lt_one_e20`, and `codySineTestExact_sineTaylorOdd5_abs_error_lt_one_e20` prove that the five-term odd Taylor polynomial approximates the reduced sine, and therefore the exact `sin(22)` target after sign transport, with error below `10^-20`, `codySineTaylorOdd5_displayedMagnitude_abs_error_lt_41e21` provides the rational interval bridge to the Table 2.4 exact-row magnitude, and `codySineTestExact_displayedTableDecimal17_abs_error_lt_half_last_place` certifies the signed displayed `sin(22)` decimal to within half of the last shown place; `codyPowerExpLogPath_eq_exact` proves the exact equality between `2.5^125` and `exp(125*log(2.5))`; `codyPowerTestExact_displayedDecimal21_abs_error_lt_half_last_place` certifies the source's 21-significant-digit decimal for `2.5^125` to within half of the last displayed place; `codyPowerTestExact_displayedTableDecimal17_abs_error_lt_half_last_place` certifies the shorter Table 2.5 exact-row decimal in the same way; `exp_absolute_error_relative_error_eq` formalizes the source sensitivity calculation `(exp(w+deltaW)-exp(w))/exp(w) = exp(deltaW)-1`; `exp_absolute_error_relative_error_abs_lt_101_mul_abs` proves the resulting relative error is below `1.01*|deltaW|` for nonzero `|deltaW| < 0.01`; `karpinskiGuardDigitProbes_equal` proves the two guard-digit probes are exactly equal over the reals; and `FloatingPointFormat.decimalOneDigitThreeExponent_karpinskiProbes_equal` gives a concrete finite round-to-even operation trace in which both Karpinski paths compute `-0.1` in the one-digit decimal format.  Open: historical machine/table outputs, full guard-digit diagnostic/test-harness semantics, and broader hardware/library execution traces. |
| 775--987 | Notes and references through monotonicity/FMA/historical notes. | Partly closed for theorem-bearing notes.  The IEEE-facing vocabulary names the rounding-mode/result/flag space needed for later tie-rule, FMA, and monotonicity statements; the overflow default-result constructor, finite mode selector, mode-aware underflow predicate, and mode-parameterized primitive-operation and square-root finite-branch dispatch are first reusable components.  `FusedMultiplyAdd.lean` formalizes the finite real-valued single-rounding FMA surface: `fusedMultiplyAddExact` is `x*y+z`, `finiteRoundToEvenFMA_eq_round_exact` exposes the one-final-rounding shape, `finiteRoundToEvenFMA_eq_exact_of_finiteSystem` proves exact representable fused results are fixed, and `finiteRoundToEvenFMA_standardModel_lt_of_finiteNormalRange` proves the strict standard-model witness in the finite-normal case.  `Chopping.lean` formalizes the finite toward-zero/chopping bias claim: nonnegative exact values have nonpositive final error, nonpositive exact values have nonnegative final error, operation wrappers in `towardZero` mode inherit that sign, and finite sums of nonnegative exact-result chopping errors remain nonpositive; it also formalizes the Vancouver three-decimal final-value floor-scaling routine `decimalChopThree`, proving exact grid values are fixed, each final error is below `0.001`, and finite accumulated final errors are nonpositive.  `TieRules.lean` formalizes the displayed decimal tie-rule chain exactly: round-to-even gives `2.445 -> 2.44 -> 2.4`, while round-to-odd gives `2.445 -> 2.45 -> 2.5`; it also proves local one-decimal add/sub traces in which round-to-even and round-to-odd are stable after the first Reiser--Knuth-shaped step, while round-away drifts from `1.1` to `1.2`.  `Nonassociativity.lean` gives no-overflow finite round-to-even counterexamples for all four primitive wrappers: `(10 ⊕ 4) ⊕ (-4) = 6` but `10 ⊕ (4 ⊕ (-4)) = 10`, `(10 ⊖ (-4)) ⊖ 4 = 6` but `10 ⊖ ((-4) ⊖ 4) = 20`, `((0.2 ⊗ 0.6) ⊗ 3) = 0.3` but `0.2 ⊗ (0.6 ⊗ 3) = 0.4`, and `(0.1 ⊘ 0.1) ⊘ 0.1 = 10` but `0.1 ⊘ (0.1 ⊘ 0.1) = 0.1`; the division example is exact-representable rather than rounding-induced.  `Monotonicity.lean` proves the local same-bracket monotonicity foundation for `nearestAdjacentRoundToEven`: on a fixed ordered adjacent bracket, increasing the exact input cannot decrease the selected endpoint.  Open: the full general Reiser--Knuth repeated add/sub tie-rule stability theorem, global finite operation monotonicity and full IEEE monotonicity, full directed operation semantics beyond primitive/square-root finite branches, the historical Vancouver Stock Exchange update-data reconstruction/full execution trace, and full IEEE FMA semantics with special values, flags, traps, signed zeros, NaNs, infinities, and payloads. |
| 988--1003 | Underflow/overflow modification (2.8) with additive `eta`, gradual-underflow bound, flush-to-zero contrast. | Partly closed.  `additiveErrorWitness`, `additiveUnderflowModelWitness`, and `strictAdditiveUnderflowModelWitness` formalize the algebraic shape `computed = exact*(1+delta)+eta`, the bounds, and the branch condition that one of `delta`/`eta` is zero.  `FloatingPointFormat.gradualUnderflowEtaBound` and `FloatingPointFormat.flushToZeroEtaBound` name the gradual-underflow `u*alpha` and flush-to-zero `alpha` bounds, and `gradualUnderflowEtaBound_eq_half_minSubnormalMagnitude` proves the gradual bound is half the subnormal spacing.  `nearestRoundingToFinite_absError_le_gradualUnderflowEtaBound_of_finiteUnderflowRange` proves the non-strict gradual-underflow absolute-error bound for finite nearest-rounded underflow outputs, and `finiteRoundToEven_additiveUnderflowModel_underflow_branch_of_finiteUnderflowRange`, `finiteRoundToEvenOp_additiveUnderflowModel_underflow_branch_of_finiteUnderflowRange`, and `finiteRoundToEvenSqrt_additiveUnderflowModel_underflow_branch_of_finiteUnderflowRange` package the additive branch for the source-facing finite wrappers.  The strict `<` variants are proved under the visible `finiteUnderflowNoHalfTie` side condition.  The no-underflow branch is also connected to the finite-normal wrappers with `eta = 0`.  The directed finite underflow selectors now give floor/ceiling subnormal-lattice branches with finite-system and one-sided/toward-zero facts.  `ieeeOverflowDefaultResult` gives an IEEE-facing default overflow result with overflow/inexact flags, `ieeeUnderflowDefaultResult` gives a finite gradual-underflow result with an underflow flag and conditional inexact flag, `ieeeUnderflowModeResult` records mode-aware finite underflow evidence, `ieeeRoundToNearestEvenOpResult_ieeeUnderflowResult_and_additiveUnderflowModel` connects nearest/even primitive-operation underflow to both the IEEE-facing result predicate and additive model witness, `ieeeRoundToModeOpResult_ieeeUnderflowModeResult_of_finiteUnderflowRange` connects all primitive rounding modes to the flagged underflow predicate, and `ieeeRoundToNearestEvenSqrtResult_ieeeUnderflowResult_and_additiveUnderflowModel` closes the nonnegative square-root underflow predicate plus additive witness.  Open: remaining special-value/trap behavior beyond the first primitive/square-root predicate branches, full IEEE operation semantics, and additive-underflow bounds for directed modes if those are desired beyond the current one-sided mode evidence. |
| 1004--1043 | Elementary function algorithms, complex functions, decimal-binary conversion and printing. | Descriptive/open.  No local correctly rounded conversion or elementary-function implementation model. |
| 1045--1175 | Problems 2.1--2.27. | Open as a problem set.  Problem 2.4 is now closed at the exercise-level finite-normal theorem surface by `problem2_4_theorem2_3_nearest_finite`, `problem2_4_theorem2_3_finiteNormalFl`, and `problem2_4_theorem2_3_finiteRoundToEven`, wrapping the underlying Theorem 2.3 inverse relative-error proof.  Problem 2.5 is closed at the finite-format theorem surface by `problem2_5_binaryOneTenth_hasSum`, `problem2_5_binaryOneTenth_tsum`, `problem2_5_ieeeSingle_roundToEven_oneTenth`, and `problem2_5_ieeeSingle_oneTenth_relative_error`: the repeating binary tail sums to `1/10`, finite IEEE-single round-to-even gives `13421773 * 2^-27`, and `(x - xhat)/x = -(1/4)u`.  Explicit IEEE operation semantics and the other problem-set items remain open. |

## Result-By-Result Ledger

| ID | Source location | Claim | Current Lean status | Next concrete target |
|---|---|---|---|---|
| C2.1 | §2.1, (2.1), lines 49--68 | Floating-point numbers have normalized finite-format representation with parameterized base, precision, and exponent range. | Closed for the normalized integer-mantissa representation.  `FloatingPointFormat` defines the source parameters, mantissa/exponent predicates, normalized/subnormal values, finite system, and unbounded normalized system.  `normalizedValue_abs_between_beta_powers` proves the per-exponent range, `normalizedValue_minNormalMantissa_abs_eq` and `normalizedValue_maxNormalMantissa_abs_eq` prove the exact endpoint formulas, `normalizedSystem_abs_bounds` proves the global finite-normalized magnitude range, and `normalizedValue_eq_iff_sign_exp_mantissa` proves uniqueness of signed normalized `(m,e)` representations. | Use the uniqueness/range facts in global nearest-rounding bracketing. |
| C2.2 | §2.1, (2.2), lines 69--78 | Positional digit representation and equivalence with (2.1). | Closed as a list-based big-endian digit-string representation.  `digitStringInRange`, `normalizedDigitString`, `positionalMantissa`, and `positionalValue` define the display form.  `positionalMantissa_normalized` sends normalized digit strings to normalized integer mantissas, `positionalValue_mem_normalizedSystem` embeds them in the normalized system, `exists_digitStringInRange_positionalMantissa_eq` and `exists_normalizedDigitString_positionalMantissa_eq` reconstruct fixed-length digit strings from mantissas, and `digitStringInRange_eq_of_positionalMantissa_eq` proves uniqueness of fixed-length digit strings with the same encoded mantissa. | Use C2.2 only as needed for examples/IEEE displays; the next finite-format theorem target is global nearest-rounding bracketing. |
| C2.3 | Lemma 2.1, lines 116--120 | Adjacent normalized spacing bounds. | Closed.  `sameExponentAdjacentNormalized`, `boundaryAdjacentNormalized`, and `adjacentNormalized` define structural normalized adjacency; `realOrderAdjacentNormalized` defines the ordered-set target; `adjacentNormalized_no_between` and `realOrderAdjacentNormalized_of_adjacentNormalized` prove structural adjacency implies ordered-set adjacency; `adjacentNormalized_of_realOrderAdjacentNormalized` proves the converse; `realOrderAdjacentNormalized_spacing_bounds_left` proves `beta^(-1) eps_M |x| <= |x-y| <= eps_M |x|` for arbitrary real-order adjacent normalized pairs. | Use this spacing theorem in the finite-format nearest-rounding proof for Theorem 2.2. |
| C2.4 | §2.1, lines 121--139 | Subnormal numbers and equal subnormal spacing. | Partly closed.  The basic subnormal magnitude, first-subnormal membership when mantissa `1` exists, sign closure, gap to the smallest normal, equal-spacing, boundary-spacing, nonzero-finite lower-bound facts, relation-valued signed subnormal nearest cells, smallest-normal boundary cells, relation-level finite-underflow nearest existence, and the floor-based source-facing underflow round-away and round-to-even selectors `finiteUnderflowRoundAway`/`finiteUnderflowRoundToEven` are proved. | Add full gradual-underflow arithmetic and IEEE underflow/exception behavior; source-facing underflow-range round-to-even is closed. |
| C2.5 | §2.1, lines 143--159 | Nearest rounding map, overflow/underflow, unit roundoff. | Partial foundation.  The nearest-rounding relations, range predicates, endpoint representability, exact self-rounding, finite output classifiers, relation-valued signed subnormal grid, finite underflow existence, global finite nearest existence, arbitrary total `finiteNearestFl`, overflow saturation, finite-normal `finiteNormalFl`, finite-normal round-away `finiteNormalRoundAway`, finite-normal round-to-even `finiteNormalRoundToEven`, finite-normal directed selectors `finiteNormalRoundTowardNegative`/`finiteNormalRoundTowardPositive`/`finiteNormalRoundTowardZero`, finite underflow directed selectors, total finite directed selectors `finiteRoundTowardNegative`/`finiteRoundTowardPositive`/`finiteRoundTowardZero`, finite mode selector `finiteRoundToMode`, total source-facing finite round-away `finiteRoundAway`, total source-facing finite round-to-even `finiteRoundToEven`, local adjacent-bracket round-to-even selector `nearestAdjacentRoundToEven`, and local adjacent-bracket directed selectors are proved.  `finiteRoundAway` is nearest for every real input and dispatches to underflow round-away, normal round-away, or overflow saturation.  `finiteRoundToEven` is nearest for every real input and exposes exact finite-normal tie branches through source evidence recording the left endpoint's mantissa parity.  The total finite directed selectors use subnormal-lattice underflow branches, finite-normal directed branches, and finite overflow saturation; toward-zero has the global finite-selector theorem `finiteRoundTowardZero_abs_le_abs`.  The IEEE wrapper layer now has mode-parameterized primitive-operation and square-root overflow/underflow/no-flags dispatch, finite underflow/no-flag branches use `finiteRoundToModeOp` and `finiteRoundToModeSqrt` through `ieeeUnderflowModeResult`, and the IEEE special-value/comparison layer has first primitive quiet-NaN and invalid-operation predicates, division-by-zero infinite-result predicates, signed-zero denominator value-selection lemmas, and ordinary finite-zero denominator default lemmas, plus modeled NaN unordered/unequal, signed-zero equality, and predicate-level comparison-completeness predicates. | Add full operational IEEE semantics, especially traps, signaling NaNs/payloads, full concrete comparison instructions beyond the predicate layer, concrete operations, full operation integration, and remaining special values. |
| C2.6 | Theorem 2.2, lines 161--180 | Rounding a real in range satisfies the forward relative-error theorem. | Closed for relation-valued finite-normal nearest rounding, arbitrary finite-normal output, arbitrary source choice `finiteNormalFl`, finite-normal round-away `finiteNormalRoundAway`, finite-normal round-to-even `finiteNormalRoundToEven`, total source-facing round-away `finiteRoundAway` restricted to finite-normal inputs, and total source-facing round-to-even `finiteRoundToEven` restricted to finite-normal inputs.  The policy surfaces include `finiteRoundAway_signedRelErrorWitness_lt_of_finiteNormalRange`, `finiteNormalRoundToEven_signedRelErrorWitness_lt`, and `finiteRoundToEven_signedRelErrorWitness_lt_of_finiteNormalRange`; the underflow and overflow branches of `finiteRoundAway` and `finiteRoundToEven` are nearest-rounded but are not part of the normal-range relative-error theorem. | Add IEEE operation-level derivation; treat underflow/IEEE behavior as C2.20/(2.8). |
| C2.7 | Theorem 2.3, lines 181--191 | Inverse relative-error representation `fl(x)=x/(1+delta)`. | Closed for finite-normal relation-valued nearest rounding, `finiteNormalFl`, `finiteNormalRoundAway`, finite-normal `finiteNormalRoundToEven`, total source-facing `finiteRoundAway` restricted to finite-normal inputs by `finiteRoundAway_inverseRelErrorWitness_of_finiteNormalRange`, and total source-facing `finiteRoundToEven` restricted to finite-normal inputs by `finiteRoundToEven_inverseRelErrorWitness_of_finiteNormalRange`.  This remains a finite-normal theorem; no inverse relative-error theorem is claimed outside the normal range. | Add remaining IEEE operation foundations or move to guard-digit foundations. |
| C2.8 | §2.1, lines 193--229 | IEEE parameters, wobbling precision, ulp. | Partly closed.  `ieeeSingleFormat`/`ieeeDoubleFormat` instantiate Higham's displayed single/double finite-format parameters; `ieeeSingleFormat_unitRoundoff`/`ieeeDoubleFormat_unitRoundoff` prove the displayed `u = 2^(-24)` and `u = 2^(-53)` values; and `ieeeSingleFormat_ulpAtExponent`/`ieeeDoubleFormat_ulpAtExponent` prove the displayed single/double ulp exponent formulas.  The generic `ulpAtExponent` API names `beta^(e-t)`, the same-exponent and boundary spacing lemmas identify adjacent gaps with that ulp, `normalizedValue_wobblingPrecision_bounds` proves the multiplicative wobbling interval around a normalized value, `realOrderAdjacentNormalized_relativeSpacing_bounds_left` proves `beta^(-1) eps_M <= abs(x-y)/abs(x) <= eps_M` for adjacent normalized endpoints, and `ieeeSingleFormat_realOrderAdjacentNormalized_relativeSpacing_bounds_left` proves the IEEE single numerical interval `2^(-24) <= abs(x-y)/abs(x) <= 2^(-23)` behind Figure 2.1.  `matlabIeeeDoubleEps` and `fortranEpsilon` record the MATLAB/Fortran machine-epsilon conventions, including `matlabIeeeDoubleEps_eq_two_zpow_neg52`, `matlabIeeeDoubleEps_eq_two_mul_ieeeDoubleFormat_unitRoundoff`, `ieeeSingleFormat_fortranEpsilon`, and `ieeeDoubleFormat_fortranEpsilon`.  The IEEE-facing vocabulary names rounding modes, exception flags, finite/signed-zero/infinite/NaN values, modeled comparison predicates, and operation results; `ieeeOverflowDefaultResult`, `ieeeUnderflowDefaultResult`, `ieeeUnderflowModeResult`, `ieeeInvalidOperationDefaultResult`, `ieeeDivisionByZeroResult`, `ieeeDivisionByZeroSignedValue`, `ieeeDivisionByZeroFiniteZeroDefaultValue`, and `IeeeOperationResult.valueNoFlags` give the first flagged and flag-free result constructors for overflow, underflow, invalid operation, finite nonzero division by zero, signed-zero denominator infinity selection, ordinary finite-zero denominator default selection, primitive quiet-NaN propagation, primitive invalid special-value inputs, modeled NaN unordered/unequal comparisons, signed-zero comparison equality, predicate-level comparison completeness, signed-zero square-root results, and non-finite square-root special values.  `ieeeRoundToModeOpResult` and the directed aliases use the rounding-mode table for primitive-operation overflow results, `ieeeRoundToModeSqrtResult` does the same for real square root, and finite underflow/no-flag branches dispatch through the finite directed selector layer.  It still does not define full IEEE arithmetic, traps, signaling-NaN/payload behavior, full concrete comparison instruction semantics beyond the predicate layer, all special-value propagation beyond signed-zero denominator division-by-zero predicate cases, or Figure 2.1 as a plotted graphic artifact. | Add full IEEE semantics. |
| C2.9 | §2.2, (2.4), lines 234--244 | Standard model for primitive operations and square root. | Partly closed.  `FPModel` gives the abstract standard model.  `finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange` and `finiteRoundToEvenSqrt_standardModel_lt_of_finiteNormalRange` derive the strict source equation from the concrete total finite round-to-even selector in ordinary finite, non-exceptional cases where the exact operation result is finite-normal.  `finiteRoundToEvenOp_eq_exact_of_finiteSystem`, `finiteRoundToEvenOp_sub_sameSign_sameExponent_eq_exact`, `finiteRoundToEvenOp_sub_positive_adjacentExponent_eq_exact_of_sterbenzAdjacent`, `finiteRoundToEvenOp_sub_positive_eq_exact_of_sterbenzRatioCondition`, `finiteRoundToEvenOp_sub_normalizedSystem_eq_exact_of_sterbenzRatioCondition`, `finiteRoundToEvenOp_sub_sameSign_subnormal_eq_exact`, `finiteRoundToEvenOp_sub_subnormalSystem_eq_exact_of_sterbenzRatioCondition`, `finiteRoundToEvenOp_sub_normalizedSystem_subnormalSystem_eq_exact_of_sterbenzRatioCondition`, `finiteRoundToEvenOp_sub_subnormalSystem_normalizedSystem_eq_exact_of_sterbenzRatioCondition`, `finiteRoundToEvenOp_sub_finiteSystem_eq_exact_of_sterbenzRatioCondition`, `finiteRoundToEvenOp_sub_eq_exact_of_guardDigitBranchSubtractionData`, `finiteRoundToEvenOp_sub_eq_exact_of_fergusonCondition`, `finiteRoundToEvenSqrt_eq_exact_of_finiteSystem`, and `finiteRoundToEvenOp_add_zero_of_finiteSystem` close exact representable results, exact guard-digit same-exponent, positive normalized Sterbenz, all-subnormal Sterbenz, and Ferguson-data subtraction, and finite left-add-zero for this real-valued finite wrapper.  `finiteRoundToModeOp` now packages source-facing finite operation rounding by mode.  `ieeeRoundToNearestEvenOpResult_ieeeOverflowResult_of_finiteOverflowRange`, `ieeeRoundToNearestEvenOpResult_ieeeUnderflowResult_of_finiteUnderflowRange`, `ieeeRoundToModeOpResult_ieeeOverflowResult_of_finiteOverflowRange`, `ieeeRoundToModeOpResult_ieeeUnderflowModeResult_of_finiteUnderflowRange`, `ieeeRoundToModeOpResult_eq_finiteNoFlags_of_not_finiteOverflowRange_of_not_finiteUnderflowRange`, and the directed alias overflow theorems give the first IEEE-facing primitive-operation overflow/underflow/no-flags branches, with mode-dependent overflow values and mode-specific primitive finite branches through `finiteRoundToModeOp`; `ieeeQuietNaNPropagationResult` and `ieeePrimitiveInvalidOperationResult` give the first primitive special-value predicate branches.  `ieeeRoundToModeSqrtResult_*` adds mode-specific square-root finite branches through `finiteRoundToModeSqrt`.  `ieeeRoundToNearestEvenSqrtResult_ieeeSqrtInvalidResult_of_neg`, `ieeeRoundToNearestEvenSqrtResult_ieeeOverflowResult_of_finiteOverflowRange`, and `ieeeRoundToNearestEvenSqrtResult_ieeeUnderflowResult_of_finiteUnderflowRange` give the finite-real square-root invalid/overflow/underflow branches.  `ieeeRoundToNearestEvenSqrtValueResult_posZero_signedZero`, `ieeeRoundToNearestEvenSqrtValueResult_negZero_signedZero`, `ieeeRoundToNearestEvenSqrtValueResult_nan_special`, `ieeeRoundToNearestEvenSqrtValueResult_posInf_special`, and `ieeeRoundToNearestEvenSqrtValueResult_negInf_special` cover the first signed-zero and non-finite square-root branches. | Extend to full IEEE operation semantics with traps, signaling NaNs/payloads, full concrete comparison instructions beyond the predicate layer, remaining special-value propagation, and concrete operation rules. |
| C2.10 | §2.2, (2.5), lines 247--260 | Modified inverse standard model. | Closed for the algebraic model and for the ordinary finite round-to-even non-exceptional operation wrappers.  `inverseRelErrorWitness` and `inverseRelErrorModel` state the source equation `fl(x)=x/(1+delta)` with `|delta| <= u`; `inverseRelErrorModel_iff_relErrorComputedDenom_le` proves its exact equivalence to the computed-denominator relative-error bound, and `inverseRelErrorModel_abs_exact_sub_computed_le` gives the absolute-error form.  The selector-level surfaces `finiteRoundToEven_inverseRelErrorWitness_of_finiteNormalRange`, `finiteRoundToEvenOp_inverseRelErrorWitness_of_finiteNormalRange`, and `finiteRoundToEvenSqrt_inverseRelErrorWitness_of_finiteNormalRange` instantiate the model for finite-normal source rounding, primitive operations, and square root. | No additional C2.10-specific Lean theorem is needed unless a future `FPModel` API must expose the inverse form directly; full IEEE exception/special-value operation semantics remain tracked under C2.8--C2.9/C2.20. |
| C2.11 | §2.4, (2.6), lines 411--464 | No-guard digit model. | Partly closed.  `noGuardAddWitness`, `noGuardSubWitness`, `noGuardMulDivWitness`, `noGuardBasicOpWitness`, and `NoGuardFPModel` formalize the displayed model (2.6a,b); `noGuardAddWitness_error_eq`, `noGuardSubWitness_error_eq`, and `noGuardMulDivWitness_error_eq` give the reusable error-split algebra; `NoGuardFPModel.exactWithUnitRoundoff` proves the abstract model is inhabited; and the binary three-digit no-guard example is closed by the four `noGuardBinaryT3_*` rational facts. | Continue with C2.12: formalize guard-digit subtraction with exponent side condition, then derive Sterbenz. |
| C2.12 | Theorem 2.4, lines 466--490 | Ferguson guard-digit exact subtraction theorem. | Partly closed as a theorem-surface interface plus the first proof reductions, both adjacent orientations, a branch implementation contract, and a noncomputable evidence-selecting branch routine.  `fergusonExponentCondition` expresses the exponent side condition using explicit normalized exponent representations; `fergusonExponentCondition_sub_not_finiteUnderflowRange` and `fergusonExponentCondition_sub_not_finiteOverflowRange` expose the finite-format side condition on `x-y`; `fergusonExponentCondition_exponent_gap_le_one` proves the source proof sentence that the exponents of `x` and `y` differ by at most one; `fergusonExponentCondition_same_sign_and_exponent_gap` proves the next source proof reduction, packaging same-sign normalized representations with the exponent-gap bounds; `fergusonExponentCondition_same_sign_exponent_cases` packages the proof branch into same-exponent or one-exponent-shift cases; `normalizedValue_sub_sameSign_sameExponent_eq_aligned` and `normalizedValue_sub_sameSign_adjacentExponent_eq_aligned` prove the raw aligned mantissa subtraction identities for those branches; `sameExponentMantissaDiffInt_cast`, `sameExponentMantissaDiffInt_natAbs_lt_mantissaBound`, `guardDigitRoundedCoeff_eq_self_of_natAbs_lt_mantissaBound`, and `normalizedValue_sub_sameSign_sameExponent_eq_guardDigitRounded` prove that the same-exponent mantissa difference has at most `t` digits and is unchanged by the modeled `t`-digit coefficient rounding; `normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_normalizedDiff` proves the same-exponent result is a finite normalized value when that exact integer mantissa difference is already normalized; `normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_beta_mul_normalizedDiff` proves the one-base-shift same-exponent result is finite normalized at exponent `e - 1` when that shifted integer difference is normalized and `e - 1` is in range; `normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_beta_pow_mul_normalizedDiff` proves the arbitrary finite radix-power shift branch under the corresponding shifted-normalized-mantissa and shifted-exponent hypotheses; `normalizedValue_sub_sameSign_sameExponent_finiteSystem_at_emin_of_natAbs_lt_minNormalMantissa` proves the same-exponent result is finite at `emin` when that exact integer difference is below the normalized leading-digit threshold, and `normalizedValue_sub_sameSign_sameExponent_finiteSystem_at_shifted_emin_of_natAbs_mul_beta_pow_lt_minNormalMantissa` proves the shifted `emin` subnormal endpoint; `guardAlignedMantissaDiffInt_cast` connects the real guard coefficient with the integer `beta*mHigh - mLow` coefficient; `guardAlignedMantissaDiffInt_natAbs_lt_minNormalMantissa_of_fergusonAdjacent` and `guardAlignedMantissaDiffInt_natAbs_lt_minNormalMantissa_of_fergusonAdjacent_reversed` prove the one-shift guard coefficient is below the normalized leading-digit threshold in both subtraction orientations; `guardDigitLeadingDigit_eq_zero_of_fergusonAdjacent` and `guardDigitTailMantissa_eq_natAbs_of_fergusonAdjacent` formalize the source proof sentence that the leading digit `z1` of the `t+1` guard word is zero and the trailing `t`-digit tail is unchanged; `normalizedValue_sub_sameSign_adjacentExponent_eq_guardDigitRounded_of_fergusonAdjacent` and `normalizedValue_sub_sameSign_reversedAdjacentExponent_eq_neg_guardDigitRounded_of_fergusonAdjacent` prove the adjacent rounded values are exact in both orientations; `guardDigitRoundedBranchSubtractionValue_eq_sub_of_ferguson`, `guardDigitBranchSubtractionModel_guardDigitSubtractionModel`, and `guardDigitBranchSubtractionModel_exact_of_fergusonCondition` prove that a routine returning the branch-level rounded values satisfies `guardDigitSubtractionModel` under Ferguson's condition; and `GuardDigitBranchSubtractionData`, `GuardDigitBranchSubtractionData.branchValue_eq_sub`, `guardDigitBranchSubtractionRoutine_branchModel`, `guardDigitBranchSubtractionRoutine_guardDigitSubtractionModel`, and `guardDigitBranchSubtractionRoutine_exact_of_fergusonCondition` instantiate that contract for a noncomputable evidence-selecting routine.  This now reaches branch finite-system output and exact concrete finite round-to-even subtraction for same-exponent normalized operands and Ferguson branch data, but is not yet a fully executable digit-level algorithm or full IEEE subtraction operation. | Prove a fully executable digit-level/full IEEE subtraction implementation and corresponding full IEEE operation theorem. |
| C2.13 | Theorem 2.5, lines 493--495 | Sterbenz exact subtraction theorem. | Partly closed with a corrected route.  `sterbenzRatioCondition` records `y/2 < x < 2*y`; positivity consequences, the ratio-distance inequalities `abs(x-y) < x`, `abs(x-y) < y`, and `abs(x-y) < min x y`, and the positive adjacent-exponent coefficient bound `guardAlignedMantissaDiffInt_natAbs_lt_mantissaBound_of_sterbenzAdjacent`, the finite-system theorem `normalizedValue_sub_positive_adjacentExponent_finiteSystem_of_sterbenzAdjacent`, the exponent-gap theorem `sterbenzRatioCondition_positive_normalized_exponent_gap_le_one`, the positive normalized finite-system theorem `normalizedValue_sub_positive_finiteSystem_of_sterbenzRatioCondition`, the normalized-system wrapper `normalizedSystem_sub_finiteSystem_of_sterbenzRatioCondition`, the all-subnormal finite-system theorem `subnormalSystem_sub_finiteSystem_of_sterbenzRatioCondition`, the mixed finite-system theorems `normalizedValue_sub_subnormalValue_positive_finiteSystem_of_sterbenzRatioCondition`, `normalizedSystem_sub_subnormalSystem_finiteSystem_of_sterbenzRatioCondition`, and `subnormalSystem_sub_normalizedSystem_finiteSystem_of_sterbenzRatioCondition`, the source-facing all-case theorem `finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition`, and the exact finite round-to-even theorems `finiteRoundToEvenOp_sub_positive_eq_exact_of_sterbenzRatioCondition`, `finiteRoundToEvenOp_sub_normalizedSystem_eq_exact_of_sterbenzRatioCondition`, and `finiteRoundToEvenOp_sub_subnormalSystem_eq_exact_of_sterbenzRatioCondition`, `finiteRoundToEvenOp_sub_normalizedSystem_subnormalSystem_eq_exact_of_sterbenzRatioCondition`, `finiteRoundToEvenOp_sub_subnormalSystem_normalizedSystem_eq_exact_of_sterbenzRatioCondition`, and `finiteRoundToEvenOp_sub_finiteSystem_eq_exact_of_sterbenzRatioCondition` close the positive normalized, all-subnormal, mixed normal/subnormal, and source-facing finite-system all-case branches; `sterbenzFergusonBridgeCondition` remains available as an explicit sufficient bridge; `guardDigitSubtractionModel_exact_of_sterbenzBridge` derives exact subtraction under that bridge; `decimalSingleDigitFormat_sterbenzRatio_not_ferguson` proves the attempted route "Sterbenz ratio implies Ferguson condition" is false in general bases; `normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_normalizedDiff` proves the same-exponent direct finite-representability branch when the exact integer mantissa difference is already normalized; `normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_beta_mul_normalizedDiff` proves the one-base-shift finite-representability branch when shifting that exact difference by one radix digit gives a normalized mantissa and exponent `e - 1` is in range; `normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_beta_pow_mul_normalizedDiff` proves the arbitrary finite radix-power shift branch under the corresponding shifted-normalized-mantissa and shifted-exponent hypotheses; and `normalizedValue_sub_sameSign_sameExponent_finiteSystem_at_emin_of_natAbs_lt_minNormalMantissa` proves the unshifted `emin` zero/subnormal endpoint, `normalizedValue_sub_sameSign_sameExponent_finiteSystem_at_shifted_emin_of_natAbs_mul_beta_pow_lt_minNormalMantissa` proves the shifted `emin` subnormal endpoint when the shifted exact integer difference is below the normalized leading-digit threshold, `sameExponentFiniteDifferenceWitness_of_normalizedMantissas` derives the selector from normalized same-exponent operands, and `finiteRoundToEvenOp_sub_sameSign_sameExponent_eq_exact` connects that branch to the concrete finite round-to-even subtraction wrapper. | Formalize a fully executable digit-level/full IEEE subtraction implementation and derive the corresponding full IEEE operation theorem. |
| C2.14 | Equation (2.7), lines 496--521 | Kahan Heron formula stability with guard digit. | Closed for the modeled finite round-to-even/no-underflow trace.  `finiteKahanHeronArea_relError_le_gamma9_unitRoundoff_of_finiteNormalRange` composes the actual finite trace, exact `a-b` Sterbenz bridge, strict finite-normal-range operation witnesses, nine-factor radicand decomposition, aggregate radicand `gamma 9` theorem, exact area factorization, and three-factor perturbation bound to prove `relError (finiteKahanHeronArea fmt a b c) (kahanHeronArea a b c) <= (1 + gamma (finiteFormatUnitRoundoffModel fmt) 9) * (1 + fmt.unitRoundoff)^2 - 1` under the explicit finite-system, finite-normal-range, nonnegative computed-radicand, and `gammaValid ... 18` hypotheses. | No C2.14-specific Lean gap remains for this modeled trace; full IEEE/underflow exception semantics are tracked under C2.19--C2.20. |
| C2.15 | §2.5, lines 523--577 | Base-choice and leading-digit distribution results. | Partly closed.  `logarithmicLeadingDigitProbability` is a finite probability law on the leading digits `1, ..., beta-1`; `logarithmicLeadingDigitProbability_prob_eq_log_div` proves each atom has the displayed Benford/logarithmic mass `log_beta ((n+1)/n)`, `logarithmicLeadingDigitMass_succ_lt` proves the masses strictly decrease as the leading digit increases, and `sum_logarithmicLeadingDigitMass_eq_one` proves normalization by telescoping.  `decimalLogarithmicLeadingDigitProbability_first_gt_last` and `decimalLogarithmicLeadingDigitProbability_nonuniform` close the source's concrete decimal nonuniformity statement.  `logarithmicIntervalMass_mul_base_pow`, `logarithmicIntervalMass_mul_base_zpow`, `logarithmicLeadingDigitMass_scaled_bin`, and `logarithmicLeadingDigitMass_scaled_bin_zpow` close the algebraic scale-invariance surface: multiplying a positive digit bin by a natural or integer power of the base leaves its logarithmic mass unchanged.  `Problem2_11.lean` now adds the empirical finite-sample surface: source-generated power/factorial samples are named, and `problem2_11_sum_digitFrequency_eq_one` plus `problem2_11_empiricalDigitProbability` prove any classified finite sample gives a normalized leading-digit distribution. | Remaining C2.15 gaps are the Brent base-optimality theorem, product-convergence and `q^k` equidistribution results, the stronger claim that scale invariance is equivalent to the observed law, actual external empirical datasets, and histogram outputs; those require separate approximation/probability/ergodic foundations or imported data. |
| C2.16 | §2.6, lines 579--631 | Statistical rounding-error model and `sqrt n` rule. | Partly closed.  `StatisticalRoundingErrorModel.rms_sum_le_sqrt_card_mul_unit` proves the finite RMS square-root rule under explicit zero-mean, pairwise-uncorrelated, bounded-second-moment assumptions.  The supporting theorem `expectation_sum_sq_eq_sum_second_moments` is the algebraic replacement for the independence/cross-term cancellation step. | Remaining C2.16 gaps are deriving the assumptions from a concrete random-rounding arithmetic, proving CLT/asymptotic normality, and formalizing PRECISE/CESTAC/logarithmic-mantissa models or leaving them explicitly descriptive. |
| C2.17 | §2.7, lines 633--690 | Alternative number systems. | Partly closed.  `AlternativeNumberSystems.lean` formalizes the precise level-index representation: iterated exponentials decode the positive-side value, iterated logarithms recover the fractional index, `LevelIndexCode` stores `l+f` with `f in [0,1]`, and `LevelIndexCode.reciprocalValue_mul_value_of_pos_level` models the reciprocal branch for `0 < x < 1`. | Remaining C2.17 material is descriptive/bibliographic unless a full alternative arithmetic is requested: range comparisons, operation-cost claims, controversy/comparative-advantage claims, Matsui--Iri variable mantissa/exponent allocation, and the other cited systems. |
| C2.18 | §2.8, lines 692--774 | Accuracy tests and tables. | Partly closed.  `AccuracyTests.lean` formalizes exact baselines and algebra for the unit-roundoff probe, Cody sine target, the reduced-argument identity, the sign/coarse magnitude bound, the five-term odd Taylor remainder below `10^-20`, the Table 2.4 exact-row `sin(22)` displayed decimal to half-last-place, Cody exponentiation test, exponentiation sensitivity identity and small-error bound, Karpinski guard-digit probes, both exact-source displayed decimals for `2.5^125`, and one concrete finite round-to-even Karpinski probe trace. | Remaining C2.18 gaps are historical machine outputs, full guard-digit diagnostic/test-harness semantics, and broader hardware/library execution traces. |
| C2.19 | §2.9, lines 775--987 | Tie rules, chopping, nonassociativity, monotonicity, FMA, historical technical claims. | Partly closed.  The IEEE vocabulary layer is started by `IeeeRoundingMode`, `IeeeExceptionFlag`, `IeeeValue`, and `IeeeOperationResult`; overflow/underflow/invalid-operation, signed-zero values, primitive quiet-NaN/invalid-operation special predicates, the first square-root signed-zero/special-value branches, mode-parameterized primitive-operation and square-root overflow dispatch, and finite directed endpoint/total selector layers have result constructors.  The FMA single-final-rounding note is now closed for the finite real-valued wrapper by `FloatingPointFormat.finiteRoundToEvenFMA_eq_round_exact`, with exact representable and finite-normal standard-model theorems.  The chopping-bias note is closed for finite toward-zero rounding by `FloatingPointFormat.finiteRoundTowardZero_error_nonpos_of_nonneg`, `FloatingPointFormat.finiteRoundToModeOp_towardZero_error_nonpos_of_exact_nonneg`, and `FloatingPointFormat.finiteRoundTowardZero_sum_errors_nonpos_of_nonneg`; the concrete Vancouver three-decimal final-value routine is closed by `decimalChopThree_abs_error_lt_one_thousandth`, `decimalChopThree_grid_eq`, `decimalChopThree_initial_index`, and `decimalChopThree_sum_errors_nonpos`.  The displayed tie-rule decimal sequence is closed by `FloatingPointFormat.decimal_2445_roundToEven_chain` and `FloatingPointFormat.decimal_2445_roundToOdd_chain`; local one-decimal add/sub stability/drift traces are closed by `FloatingPointFormat.decimalOnePlaceRoundToEven_reiserKnuth_stable_from_one`, `FloatingPointFormat.decimalOnePlaceRoundToOdd_reiserKnuth_stable_after_first_step`, and `FloatingPointFormat.decimalOnePlaceRoundAway_drift_first_two_steps`.  Rounded primitive-wrapper nonassociativity is closed for addition, subtraction, multiplication, and division by `FloatingPointFormat.decimalOneDigitTwoExponent_roundToEven_add_nonassociative`, `FloatingPointFormat.decimalOneDigitTwoExponent_roundToEven_sub_nonassociative`, `FloatingPointFormat.decimalOneDigitThreeExponent_roundToEven_mul_nonassociative`, and `FloatingPointFormat.decimalOneDigitThreeExponent_roundToEven_div_nonassociative`.  Local adjacent-bracket round-to-even monotonicity is closed by `FloatingPointFormat.nearestAdjacentRoundToEven_monotone_on_ordered_bracket`. | Remaining C2.19 theorem targets are the full general Reiser--Knuth repeated add/sub tie-rule stability theorem, global finite operation monotonicity and full IEEE monotonicity, full directed operation semantics beyond primitive/square-root finite branches, the historical Vancouver Stock Exchange update-data reconstruction/full execution trace, and full IEEE FMA/special-value semantics. |
| C2.20 | §2.9, (2.8), lines 988--1003 | Underflow-aware model with additive `eta`. | Partly closed.  The algebraic additive witness predicates and branch constructors are proved in `Error.lean`; the finite-format gradual/flush eta bounds are named in `FloatingPointArithmetic.lean`; `unitRoundoff_mul_minNormalMagnitude_eq_half_minSubnormalMagnitude` proves the source identity that `u*alpha` is half the subnormal spacing; the normal branch of (2.8) is connected to the finite-normal round-to-even selector, primitive-operation wrapper, and square-root wrapper; the non-strict gradual-underflow additive branch is proved for finite nearest-rounded underflow outputs and the source-facing finite round-to-even/op/sqrt wrappers; strict `<` variants are proved under `finiteUnderflowNoHalfTie`; the source-facing finite wrappers are embedded as finite, flag-free IEEE-facing results; `ieeeOverflowDefaultResult_ieeeOverflowResult_of_finiteOverflowRange` closes the first flagged overflow-result constructor; `ieeeUnderflowDefaultResult_ieeeUnderflowResult` closes the nearest/even flagged underflow-result constructor; `ieeeUnderflowDefaultResult_ieeeUnderflowModeResult`, `ieeeRoundToModeOpResult_ieeeUnderflowModeResult_of_finiteUnderflowRange`, and `ieeeRoundToModeSqrtResult_ieeeUnderflowModeResult_of_finiteUnderflowRange` close the mode-aware primitive-operation and square-root flagged underflow predicates; and `ieeeRoundToNearestEvenOpResult_ieeeUnderflowResult_and_additiveUnderflowModel` plus `ieeeRoundToNearestEvenSqrtResult_ieeeUnderflowResult_and_additiveUnderflowModel` close the nearest/even primitive-operation and nonnegative square-root underflow dispatches plus additive witnesses. | Integrate traps and broader IEEE special values into full IEEE operation semantics, or prove directed-mode additive-underflow bounds if needed beyond the current one-sided mode evidence. |
| C2.21 | Problems 2.1--2.27, lines 1045--1175 | Exercises and concrete IEEE questions. | Partly closed.  Problem 2.1 is closed for the repository's inclusive finite-format value-count layer by `normalizedNumberParameterCount_eq_problem2_1_formula`, `subnormalNumberParameterCount_eq_problem2_1_formula`, `problem2_1_ieeeSingle_normalizedNumberParameterCount`, `problem2_1_ieeeSingle_subnormalNumberParameterCount`, `problem2_1_ieeeDouble_normalizedNumberParameterCount`, and `problem2_1_ieeeDouble_subnormalNumberParameterCount`: the signed nonzero normalized count is `2 * (emax - emin + 1) * (beta^t - beta^(t-1))`, the signed nonzero subnormal count is `2 * (beta^(t-1) - 1)`, IEEE single has `4,261,412,864` normalized and `16,777,214` subnormal values, and IEEE double has `18,428,729,675,200,069,632` normalized and `9,007,199,254,740,990` subnormal values.  Problem 2.2 is closed as the exercise-level proof of Lemma 2.1 by `problem2_2_lemma2_1_spacing_bounds_left`, `problem2_2_lemma2_1_spacing_bounds_right`, and `problem2_2_lemma2_1_spacing_bounds`, wrapping `realOrderAdjacentNormalized_spacing_bounds_left` for both adjacent normalized endpoints.  Problem 2.3 now has normalized same-exponent and exponent-boundary signed branches by `problem2_3_sameExponentInteriorDoubleMantissas_card`, `problem2_3_boundaryInteriorDoubleMantissas_card`, `problem2_3_ieeeDouble_between_adjacent_ieeeSingle_sameExponent_signed`, and `problem2_3_ieeeDouble_between_adjacent_ieeeSingle_boundary_signed`: each normalized branch has `2^29 - 1` scaled interior double mantissas, and every listed interior mantissa gives a finite IEEE-double value strictly between the corresponding signed adjacent normalized IEEE-single endpoints.  It also has the dyadic-block subnormal grid branch by `problem2_3_subnormalBlockInteriorDoubleMantissas_card` and `problem2_3_ieeeDouble_between_ieeeSingle_subnormal_block_signed`: for `s <= 22`, `2^s <= m`, and `m+1 <= 2^(s+1)`, the listed interior double mantissas have scale `2^(52-s)` and cardinality `2^(52-s)-1`, and each listed mantissa is a finite IEEE-double value strictly between the corresponding signed single-subnormal grid endpoints; the first positive subnormal theorem `problem2_3_ieeeDouble_between_first_two_ieeeSingle_subnormals` is the `s = 0`, `m = 1` specialization with count `2^52 - 1`.  The source-facing normalized endpoint coverage theorem is closed by `problem2_3_exists_adjacentSingleGap_of_ieeeSingle_realOrderAdjacentNormalized_ordered` and `problem2_3_exists_adjacentSingleGap_of_ieeeSingle_realOrderAdjacentNormalized`: arbitrary finite IEEE-single normalized endpoints that are adjacent in the repository's real-order normalized vocabulary are represented by one of the branch-family constructors.  Problem 2.4 is closed as the exercise-level proof of Theorem 2.3 by `problem2_4_theorem2_3_nearest_finite`, `problem2_4_theorem2_3_finiteNormalFl`, and `problem2_4_theorem2_3_finiteRoundToEven`, exposing `fl(x) = x/(1+delta)` with `|delta| <= u` on the finite-normal theorem range.  Problem 2.5 is closed at the finite-format theorem surface by `problem2_5_binaryOneTenth_hasSum`, `problem2_5_binaryOneTenth_tsum`, `problem2_5_ieeeSingle_roundToEven_oneTenth`, and `problem2_5_ieeeSingle_oneTenth_relative_error`: the repeating binary tail sums to `1/10`, finite IEEE-single round-to-even gives `13421773 * 2^-27`, and `(x - xhat)/x = -(1/4)u` with `u = 2^-24`.  Problem 2.6 is closed at the finite-format theorem surface by `problem2_6_ieeeSingle_largest_integer_interval` and `problem2_6_ieeeDouble_largest_integer_interval`: every integer in `[-2^24,2^24]` is exactly representable in IEEE single and every integer in `[-2^53,2^53]` is exactly representable in IEEE double, while `2^24+1` and `2^53+1` are proved nonrepresentable.  Problem 2.7 now has finite round-to-even theorem surfaces for statements 1, 3, and 4: `finiteRoundToEvenOp_add_comm`, `finiteRoundToEvenOp_mul_comm`, `finiteRoundToEvenOp_add_self_eq_mul_two`, and `finiteRoundToEvenOp_half_mul_eq_div_two`; statement 2 is closed for the total finite selector under even radix and `1 < t` by `problem2_7_statement2_sub_sign_symmetry`, with `problem2_7_statement2_sub_sign_symmetry_of_exact_finiteSystem` and `problem2_7_statement2_sub_sign_symmetry_of_not_finiteNormalRange` kept as reusable branch lemmas; statement 5 is refuted at the finite-operation layer by `problem2_7_statement5_add_associativity_false`, and statement 6 is refuted by `problem2_7_statement6_midpoint_strict_between_false`.  Problem 2.8's base-10 violation is closed by `problem2_8_decimal_midpoint_strict_between_violated`: in the one-digit decimal format, `1` and `2` are floating-point numbers with `1 < 2`, but `fl((1+2)/2) = 2`, so the strict-between claim fails.  Problem 2.9's general double-rounding warning has a finite-format witness: `binaryDoubleRounding_counterexample` proves that `21/16` rounded through a binary `t = 3` extended format and then a binary `t = 2` destination format gives a different result from direct `t = 2` rounding.  The actual Problem 2.9 expression is now closed at the finite-selector layer: `problem2_9_direct_double_rounds_to_predecessor` and `problem2_9_direct_double_sqrt_rounds_to_predecessor` prove direct IEEE-double finite round-to-even gives `1 - 2^-53`; `problem2_9_extended64_rounds_to_double_midpoint` proves first rounding to the local 64-bit-mantissa extended format gives `1 - 2^-54`; and `problem2_9_double_rounding_from_extended64` plus `problem2_9_direct_double_ne_double_rounded_extended64` prove the double-rounded result is `1` and differs from direct rounding.  Problem 2.10's displayed Kahan theorem instance is closed at the finite-selector layer by `problem2_10_ieeeDouble_oneThird_rounds_to_lower`, `problem2_10_ieeeDouble_div_one_three`, `problem2_10_ieeeDouble_rounded_oneThird_mul_three_midpoint`, `problem2_10_ieeeDouble_midpoint_below_one_rounds_to_one`, and `problem2_10_ieeeDouble_one_third_times_three`: finite IEEE-double round-to-even proves `fl((1/3)*3) = 1`. | Continue the problem-by-problem module.  Problem 2.8's concrete full guard-digit/IEEE operation-semantics lift beyond the exact-step theorem surface, the remaining nonzero-numerator quantified Problem 2.10 Kahan theorem for non-representable quotients with eligible integer `m` and `n = 2^i + 2^j`, the remaining exercises, and full IEEE operation semantics with flags/traps/special values are still open. |

Problem 2.10 displayed Kahan update: `problem2_10_allowableDenominator`,
`problem2_10_displayedAllowableDenominatorPrefix`, and
`problem2_10_displayedAllowableDenominatorPrefix_allowable` formalize the
source's displayed initial allowable-denominator sequence
`1,2,3,4,5,6,8,9,10,12,16,17,18,20` at the integer-side shape
`n = 2^i + 2^j`, using rational powers so the leading `1` is represented by
`2^-1 + 2^-1`.  `problem2_10_allowableDenominator_of_nat_power_sum`
connects the natural-exponent special case to that rational-exponent source
predicate, and `problem2_10_allowableDenominator_ne_zero` proves that every
allowable denominator is nonzero.  The generic power-of-two dependency is now
partly closed:
`problem2_10_powerOfTwo_numerator_kahan_hypotheses` and
`problem2_10_negative_powerOfTwo_numerator_kahan_hypotheses` prove that, for
every `k < ieeeDoubleFormat.t - 1`, the denominator-`3` pairs
`m = 2^k` and `m = -2^k` satisfy the quoted integer-side Kahan hypotheses;
`problem2_10_powerOfTwo_numerator_kahan_hypotheses_of_allowableDenominator`
and
`problem2_10_negative_powerOfTwo_numerator_kahan_hypotheses_of_allowableDenominator`
generalize those integer-side power-of-two numerator hypotheses to arbitrary
allowable denominators;
`problem2_10_ieeeDouble_two_pow_le_maxFiniteMagnitude` and
`problem2_10_ieeeDouble_two_pow_div_three_finiteNormalRange` prove the reusable
IEEE-double range facts that `2^k` is below the finite maximum for `k <= 1023`
and `(2^k)/3` is finite-normal in the same range, while
`problem2_10_ieeeDouble_two_pow_thirds_rounds_to_lower` proves the reusable
first rounding fact
`fl((2^k)/3) = 6004799503160661 * 2^(k-54)` in that range.
`problem2_10_ieeeDouble_div_two_pow_three`,
`problem2_10_ieeeDouble_rounded_two_pow_thirds_mul_three_midpoint`, and
`problem2_10_ieeeDouble_div_two_pow_three_exact_mul_three_midpoint` lift this
to the operation wrapper and prove that the exact product with `3` is the
midpoint `2^k - 2^(k-54)` immediately below `2^k`;
`problem2_10_ieeeDouble_midpoint_below_two_pow_rounds_to_two_pow` proves the
generic final tie-to-even fact at that power-of-two boundary; and
`problem2_10_ieeeDouble_two_pow_thirds_times_three` packages the positive
finite-selector trace `fl(((2^k)/3)*3) = 2^k` for every `k <= 1023`.  The
signed companion is closed by `problem2_10_ieeeDouble_div_neg_two_pow_three`,
`problem2_10_ieeeDouble_negative_rounded_two_pow_thirds_mul_three_midpoint`,
`problem2_10_ieeeDouble_div_neg_two_pow_three_exact_mul_three_midpoint`,
`problem2_10_ieeeDouble_negative_midpoint_above_two_pow_rounds_to_neg_two_pow`,
`problem2_10_ieeeDouble_neg_two_pow_thirds_times_three`, and
`problem2_10_ieeeDouble_signed_two_pow_thirds_times_three`, proving
`fl(((-2^k)/3)*3) = -2^k` by round-to-even oddness.  These
facts remove one repeated case-by-case side-condition, first-rounding,
exact-product, and final-rounding layer from the route to the quantified
denominator-`3` theorem.
`problem2_10_displayed_denominator_eq_power_sum`, the twelve
displayed numerator-hypothesis theorems for `m = ±1, ±2, ±4, ±8, ±16, ±32`,
and the finite-system/trace-input certificates prove that those signed `n = 3`
pairs satisfy the quoted integer-side Kahan hypotheses and have finite
IEEE-double operands plus finite first rounded intermediates.  The
zero-numerator branch is closed generically by
`problem2_10_finiteRoundToEven_zero_div_mul` and in source-shaped IEEE-double
form by `problem2_10_ieeeDouble_zero_allowable_denominator_times_denominator`:
for every nonzero natural denominator satisfying `problem2_10_allowableDenominator`,
the modeled finite-selector computation `fl((0/n)*n)` returns `0`.  The
wrapper `problem2_10_ieeeDouble_zero_allowable_denominator_times_denominator'`
removes the separate nonzero hypothesis using
`problem2_10_allowableDenominator_ne_zero`.  The exact-quotient operation
route is also closed by
`problem2_10_finiteRoundToEven_div_mul_exact_of_finiteSystem` and
`problem2_10_ieeeDouble_allowable_denominator_exact_quotient_trace`: for any
allowable denominator, if `m/n` and `m` are already finite representable, then
the finite round-to-even division/multiplication sequence returns `m`.
The first non-representable quotient instance beyond denominator `3` is now
closed for the source-prefix denominator `5`: `problem2_10_denominator_five_eq_power_sum`
and `problem2_10_five_allowableDenominator` prove the source denominator shape,
`problem2_10_one_fifth_kahan_hypotheses` and
`problem2_10_negative_one_fifth_kahan_hypotheses` prove the integer-side
hypotheses for `m = +/-1`, and the finite-input certificates include the
denominator `5`.  The rounded trace is result-by-result:
`problem2_10_ieeeDouble_oneFifth_rounds_to_upper` proves
`fl(1/5) = 7205759403792794 * 2^-55`,
`problem2_10_ieeeDouble_div_one_five_exact_mul_five_above_one` proves the
exact product with `5` is `1 + 2^-54`, and
`problem2_10_ieeeDouble_one_plus_two_pow_neg54_rounds_to_one` proves this
rounds back to `1`; the signed companion is packaged by
`problem2_10_ieeeDouble_signed_one_fifth_times_five`.
The next numerator magnitude for denominator `5` is also closed:
`problem2_10_two_fifth_kahan_hypotheses` and
`problem2_10_negative_two_fifth_kahan_hypotheses` prove the integer-side
hypotheses for `m = +/-2`, and
`problem2_10_ieeeDouble_two_fifth_trace_finite_inputs` plus
`problem2_10_ieeeDouble_neg_two_fifth_trace_finite_inputs` record the
finite-input audit.  The rounded trace is again result-by-result:
`problem2_10_ieeeDouble_twoFifths_rounds_to_upper` proves
`fl(2/5) = 7205759403792794 * 2^-54`,
`problem2_10_ieeeDouble_div_two_five_exact_mul_five_above_two` proves the
exact product with `5` is `2 + 2^-53`, and
`problem2_10_ieeeDouble_two_plus_two_pow_neg53_rounds_to_two` proves this
rounds back to `2`; the signed companion is packaged by
`problem2_10_ieeeDouble_signed_two_fifth_times_five`.
The first denominator-`5` non-power-of-two numerator route is now closed:
`problem2_10_three_fifth_kahan_hypotheses` and
`problem2_10_negative_three_fifth_kahan_hypotheses` prove the integer-side
hypotheses for `m = +/-3`, and
`problem2_10_ieeeDouble_three_fifth_trace_finite_inputs` plus
`problem2_10_ieeeDouble_neg_three_fifth_trace_finite_inputs` record the
finite-input audit.  The rounded trace is result-by-result:
`problem2_10_ieeeDouble_threeFifths_rounds_to_lower` proves
`fl(3/5) = 5404319552844595 * 2^-53`,
`problem2_10_ieeeDouble_div_three_five_exact_mul_five_below_three` proves the
exact product with `5` is `3 - 2^-53`, and
`problem2_10_ieeeDouble_three_minus_two_pow_neg53_rounds_to_three` proves this
rounds back to `3`; the signed companion is packaged by
`problem2_10_ieeeDouble_signed_three_fifth_times_five`.
The same non-power-of-two route is now scaled by powers of two:
`problem2_10_three_mul_powerOfTwo_numerator_kahan_hypotheses_of_five` and
`problem2_10_negative_three_mul_powerOfTwo_numerator_kahan_hypotheses_of_five`
prove the source integer-side hypotheses for `m = +/-3*2^k` under the source
size condition `k + 2 < ieeeDoubleFormat.t`.
`problem2_10_ieeeDouble_three_mul_two_pow_div_five_finiteNormalRange` proves
the first quotient is finite-normal,
`problem2_10_ieeeDouble_three_mul_two_pow_fifths_rounds_to_lower` proves
`fl((3*2^k)/5) = 5404319552844595 * 2^(k-53)`,
`problem2_10_ieeeDouble_div_three_mul_two_pow_five_exact_mul_five_below`
proves the exact product with `5` is `3*2^k - 2^(k-53)`, and
`problem2_10_ieeeDouble_three_mul_two_pow_minus_quarter_ulp_rounds` proves the
final quarter-ulp-below value rounds back to `3*2^k` for `k <= 1021`; the
signed operation wrapper is packaged by
`problem2_10_ieeeDouble_signed_three_mul_two_pow_fifths_times_five`.
The denominator-`5` power-of-two numerator subfamily is now closed in the
finite-selector model: `problem2_10_ieeeDouble_two_pow_div_five_finiteNormalRange`
proves `(2^k)/5` is finite-normal for `k <= 1023`,
`problem2_10_ieeeDouble_two_pow_fifths_rounds_to_upper` proves the first
rounding
`fl((2^k)/5) = 7205759403792794 * 2^(k-55)`,
`problem2_10_ieeeDouble_div_two_pow_five_exact_mul_five_above_two_pow`
proves the exact product with `5` is `2^k + 2^(k-54)`, and
`problem2_10_ieeeDouble_two_pow_plus_quarter_ulp_rounds_to_two_pow` proves the
final quarter-ulp value rounds back to `2^k` for `k <= 1022`.  The signed
operation wrapper is packaged by
`problem2_10_ieeeDouble_signed_two_pow_fifths_times_five`.
The next displayed-prefix denominator is also closed for shifted
power-of-two numerators: `problem2_10_denominator_six_eq_power_sum` and
`problem2_10_six_allowableDenominator` prove `6 = 2^2 + 2^1`, while
`problem2_10_ieeeDouble_div_two_pow_succ_six` proves the first rounded
division reuses the denominator-`3` quotient for `(2^k)/3`.
`problem2_10_ieeeDouble_div_two_pow_succ_six_exact_mul_six_midpoint` proves
the exact product with `6` is the midpoint
`2^(k+1) - 2^((k+1)-54)`, and
`problem2_10_ieeeDouble_signed_two_pow_succ_sixths_times_six` packages the
signed finite-selector trace
`fl(((+/-2^(k+1))/6)*6) = +/-2^(k+1)` for `k <= 1022`.
The denominator-`6`, numerator-`1` case left outside that shifted-power family
is now closed as well: `problem2_10_one_sixth_kahan_hypotheses` and
`problem2_10_negative_one_sixth_kahan_hypotheses` prove the source
integer-side hypotheses for `m = +/-1`, `problem2_10_ieeeDouble_oneSixth_rounds_to_lower`
proves `fl(1/6) = 6004799503160661 * 2^-55`,
`problem2_10_ieeeDouble_div_one_six_exact_mul_six_midpoint` proves the exact
product with `6` is `1 - 2^-54`, and
`problem2_10_ieeeDouble_signed_one_sixth_times_six` packages the final
finite-selector trace `fl(((+/-1)/6)*6) = +/-1` by the same tie-to-even
midpoint and signed-oddness route.
The next displayed-prefix denominator is now closed for two denominator-`10`
frontier branches:
`problem2_10_denominator_ten_eq_power_sum` and
`problem2_10_ten_allowableDenominator` prove `10 = 2^3 + 2^1`;
`problem2_10_one_tenth_kahan_hypotheses` and
`problem2_10_negative_one_tenth_kahan_hypotheses` prove the source
integer-side hypotheses for `m = +/-1`.  The rounded trace is
result-by-result: `problem2_10_ieeeDouble_oneTenth_rounds_to_upper` proves
`fl(1/10) = 7205759403792794 * 2^-56`,
`problem2_10_ieeeDouble_div_one_ten_exact_mul_ten_above_one` proves the exact
product with `10` is `1 + 2^-54`, and
`problem2_10_ieeeDouble_signed_one_tenth_times_ten` packages the final
finite-selector trace `fl(((+/-1)/10)*10) = +/-1` using the denominator-`5`
final-rounding cell and signed oddness.  The shifted power-of-two numerator
branch is also closed: `problem2_10_two_pow_succ_numerator_kahan_hypotheses_of_ten`
and `problem2_10_negative_two_pow_succ_numerator_kahan_hypotheses_of_ten`
prove the source integer-side hypotheses for `m = +/-2^(k+1)` under
`k + 2 < ieeeDoubleFormat.t`;
`problem2_10_ieeeDouble_div_two_pow_succ_ten` proves the first rounded division
reuses the denominator-`5` quotient for `(2^k)/5`;
`problem2_10_ieeeDouble_div_two_pow_succ_ten_exact_mul_ten_above` proves the
exact product with `10` is `2^(k+1) + 2^((k+1)-54)`; and
`problem2_10_ieeeDouble_signed_two_pow_succ_tenths_times_ten` packages the
signed finite-selector trace
`fl(((+/-2^(k+1))/10)*10) = +/-2^(k+1)` for `k <= 1021`.
The displayed-prefix denominator `9` is now closed for power-of-two numerators:
`problem2_10_denominator_nine_eq_power_sum` and
`problem2_10_nine_allowableDenominator` prove `9 = 2^3 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_nine` and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_nine` prove the
source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_ninths_rounds_to_lower` proves the first
rounded division sends `(2^k)/9` to
`8006399337547548 * 2^(k-56)`;
`problem2_10_ieeeDouble_div_two_pow_nine_exact_mul_nine_midpoint` proves the
exact product with `9` is the midpoint `2^k - 2^(k-54)`; and
`problem2_10_ieeeDouble_signed_two_pow_ninths_times_nine` packages the signed
finite-selector trace
`fl(((+/-2^k)/9)*9) = +/-2^k` for `k <= 1023`.
The genuinely new displayed-prefix denominator `17` is now closed for
power-of-two numerators: `problem2_10_denominator_seventeen_eq_power_sum` and
`problem2_10_seventeen_allowableDenominator` prove `17 = 2^4 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_seventeen` and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_seventeen` prove
the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_seventeenths_rounds_to_lower` proves the first
rounded division sends `(2^k)/17` to
`8477364004462110 * 2^(k-57)`;
`problem2_10_ieeeDouble_div_two_pow_seventeen_exact_mul_seventeen_below`
proves the exact product with `17` is
`2^k - 2^(k-56)`, one sixteenth of an ulp below `2^k`;
`problem2_10_ieeeDouble_two_pow_minus_one_sixteenth_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_seventeenths_times_seventeen` packages
the signed finite-selector trace
`fl(((+/-2^k)/17)*17) = +/-2^k` for `k <= 1023`.
The next genuinely new odd denominator `33` is now closed for power-of-two
numerators: `problem2_10_denominator_thirtythree_eq_power_sum` and
`problem2_10_thirtythree_allowableDenominator` prove `33 = 2^5 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_thirtythree` and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_thirtythree` prove
the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_thirtythirds_rounds_to_upper` proves the first
rounded division sends `(2^k)/33` to
`8734253822779144 * 2^(k-58)`;
`problem2_10_ieeeDouble_div_two_pow_thirtythree_exact_mul_thirtythree_above`
proves the exact product with `33` is
`2^k + 2^(k-55)`, one eighth of an ulp above `2^k`;
`problem2_10_ieeeDouble_two_pow_plus_one_eighth_ulp_rounds_to_two_pow` proves
the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_thirtythirds_times_thirtythree`
packages the signed finite-selector trace
`fl(((+/-2^k)/33)*33) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `65` is now closed for power-of-two
numerators: `problem2_10_denominator_sixtyfive_eq_power_sum` and
`problem2_10_sixtyfive_allowableDenominator` prove `65 = 2^6 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_sixtyfive` and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_sixtyfive` prove
the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_sixtyfifths_rounds_to_upper` proves the first
rounded division sends `(2^k)/65` to
`8868626958514208 * 2^(k-59)`;
`problem2_10_ieeeDouble_div_two_pow_sixtyfive_exact_mul_sixtyfive_above`
proves the exact product with `65` is
`2^k + 2^(k-54)`, one quarter of an ulp above `2^k`;
the already proved
`problem2_10_ieeeDouble_two_pow_plus_quarter_ulp_rounds_to_two_pow` proves the
final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_sixtyfifths_times_sixtyfive` packages
the signed finite-selector trace
`fl(((+/-2^k)/65)*65) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `129` is now closed for power-of-two
numerators: `problem2_10_denominator_onehundredtwentynine_eq_power_sum` and
`problem2_10_onehundredtwentynine_allowableDenominator` prove
`129 = 2^7 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_onehundredtwentynine` and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_onehundredtwentynine`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_onehundredtwentyninths_rounds_to_lower`
proves the first rounded division sends `(2^k)/129` to
`8937376004704240 * 2^(k-60)`;
`problem2_10_ieeeDouble_div_two_pow_onehundredtwentynine_exact_mul_onehundredtwentynine_below`
proves the exact product with `129` is
`2^k - 2^(k-56)`, one sixteenth of an ulp below `2^k`;
the already proved
`problem2_10_ieeeDouble_two_pow_minus_one_sixteenth_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_onehundredtwentyninths_times_onehundredtwentynine`
packages the signed finite-selector trace
`fl(((+/-2^k)/129)*129) = +/-2^k` for `k <= 1023`.
The next genuinely new odd denominator `257` is now closed for power-of-two
numerators: `problem2_10_denominator_twohundredfiftyseven_eq_power_sum` and
`problem2_10_twohundredfiftyseven_allowableDenominator` prove
`257 = 2^8 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_twohundredfiftyseven` and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_twohundredfiftyseven`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_twohundredfiftysevenths_rounds_to_upper`
proves the first rounded division sends `(2^k)/257` to
`8972151786823712 * 2^(k-61)`;
`problem2_10_ieeeDouble_div_two_pow_twohundredfiftyseven_exact_mul_twohundredfiftyseven_above`
proves the exact product with `257` is
`2^k + 2^(k-56)`, one sixteenth of an ulp above `2^k`;
the new
`problem2_10_ieeeDouble_two_pow_plus_one_sixteenth_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_twohundredfiftysevenths_times_twohundredfiftyseven`
packages the signed finite-selector trace
`fl(((+/-2^k)/257)*257) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `513` is now closed for power-of-two
numerators: `problem2_10_denominator_fivehundredthirteen_eq_power_sum` and
`problem2_10_fivehundredthirteen_allowableDenominator` prove
`513 = 2^9 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_fivehundredthirteen` and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_fivehundredthirteen`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_fivehundredthirteenths_rounds_to_lower`
proves the first rounded division sends `(2^k)/513` to
`8989641361456896 * 2^(k-62)`;
`problem2_10_ieeeDouble_div_two_pow_fivehundredthirteen_exact_mul_fivehundredthirteen_midpoint`
proves the exact product with `513` is the midpoint
`2^k - 2^(k-54)`; the already proved
`problem2_10_ieeeDouble_midpoint_below_two_pow_rounds_to_two_pow` proves the
final tie-to-even round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_fivehundredthirteenths_times_fivehundredthirteen`
packages the signed finite-selector trace
`fl(((+/-2^k)/513)*513) = +/-2^k` for `k <= 1023`.
The next genuinely new odd denominator `1025` is now closed for power-of-two
numerators: `problem2_10_denominator_onethousandtwentyfive_eq_power_sum` and
`problem2_10_onethousandtwentyfive_allowableDenominator` prove
`1025 = 2^10 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_onethousandtwentyfive` and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_onethousandtwentyfive`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_onethousandtwentyfifths_rounds_to_lower`
proves the first rounded division sends `(2^k)/1025` to
`8998411743272952 * 2^(k-63)`;
`problem2_10_ieeeDouble_div_two_pow_onethousandtwentyfive_exact_mul_onethousandtwentyfive_below`
proves the exact product with `1025` is
`2^k - 2^(k-60)`; the new
`problem2_10_ieeeDouble_two_pow_minus_one_twohundredfiftysixth_ulp_rounds_to_two_pow`
proves the final round returns `2^k` because that exact product is strictly
closer to `2^k` than to the previous double; and
`problem2_10_ieeeDouble_signed_two_pow_onethousandtwentyfifths_times_onethousandtwentyfive`
packages the signed finite-selector trace
`fl(((+/-2^k)/1025)*1025) = +/-2^k` for `k <= 1023`.
The next genuinely new odd denominator `2049` is now closed for power-of-two
numerators: `problem2_10_denominator_twothousandfortynine_eq_power_sum` and
`problem2_10_twothousandfortynine_allowableDenominator` prove
`2049 = 2^11 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_twothousandfortynine` and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_twothousandfortynine`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_twothousandfortyninths_rounds_to_upper`
proves the first rounded division sends `(2^k)/2049` to
`9002803354665472 * 2^(k-64)`;
`problem2_10_ieeeDouble_div_two_pow_twothousandfortynine_exact_mul_twothousandfortynine_above`
proves the exact product with `2049` is
`2^k + 2^(k-55)`; the already proved
`problem2_10_ieeeDouble_two_pow_plus_one_eighth_ulp_rounds_to_two_pow`
proves the final round returns `2^k` because that exact product is one eighth
of an ulp above `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_twothousandfortyninths_times_twothousandfortynine`
packages the signed finite-selector trace
`fl(((+/-2^k)/2049)*2049) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `4097` is now closed for power-of-two
numerators: `problem2_10_denominator_fourthousandninetyseven_eq_power_sum`
and `problem2_10_fourthousandninetyseven_allowableDenominator` prove
`4097 = 2^12 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_fourthousandninetyseven`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_fourthousandninetyseven`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_fourthousandninetysevenths_rounds_to_upper`
proves the first rounded division sends `(2^k)/4097` to
`9005000768225312 * 2^(k-65)`;
`problem2_10_ieeeDouble_div_two_pow_fourthousandninetyseven_exact_mul_fourthousandninetyseven_above`
proves the exact product with `4097` is
`2^k + 2^(k-60)`; the new
`problem2_10_ieeeDouble_two_pow_plus_one_twohundredfiftysixth_ulp_rounds_to_two_pow`
proves the final round returns `2^k` because that exact product is one 256th
of an ulp above `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_fourthousandninetysevenths_times_fourthousandninetyseven`
packages the signed finite-selector trace
`fl(((+/-2^k)/4097)*4097) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `8193` is now closed for power-of-two
numerators: `problem2_10_denominator_eightthousandonehundredninetythree_eq_power_sum`
and `problem2_10_eightthousandonehundredninetythree_allowableDenominator`
prove `8193 = 2^13 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_eightthousandonehundredninetythree`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_eightthousandonehundredninetythree`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_eightthousandonehundredninetythirds_rounds_to_upper`
proves the first rounded division sends `(2^k)/8193` to
`9006099877314562 * 2^(k-66)`;
`problem2_10_ieeeDouble_div_two_pow_eightthousandonehundredninetythree_exact_mul_eightthousandonehundredninetythree_above`
proves the exact product with `8193` is
`2^k + 2^(k-65)`; the new
`problem2_10_ieeeDouble_two_pow_plus_one_eightthousandonehundredninetysecond_ulp_rounds_to_two_pow`
proves the final round returns `2^k` because that exact product is one 8192nd
of an ulp above `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_eightthousandonehundredninetythirds_times_eightthousandonehundredninetythree`
packages the signed finite-selector trace
`fl(((+/-2^k)/8193)*8193) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `16385` is now closed for power-of-two
numerators: `problem2_10_denominator_sixteenthousandthreehundredeightyfive_eq_power_sum`
and `problem2_10_sixteenthousandthreehundredeightyfive_allowableDenominator`
prove `16385 = 2^14 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_sixteenthousandthreehundredeightyfive`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_sixteenthousandthreehundredeightyfive`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_sixteenthousandthreehundredeightyfifths_rounds_to_lower`
proves the first rounded division sends `(2^k)/16385` to
`9006649532479488 * 2^(k-67)`;
`problem2_10_ieeeDouble_div_two_pow_sixteenthousandthreehundredeightyfive_exact_mul_sixteenthousandthreehundredeightyfive_below`
proves the exact product with `16385` is
`2^k - 2^(k-56)`; the already proved
`problem2_10_ieeeDouble_two_pow_minus_one_sixteenth_ulp_rounds_to_two_pow`
proves the final round returns `2^k` because that exact product is one eighth
of the lower ulp below `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_sixteenthousandthreehundredeightyfifths_times_sixteenthousandthreehundredeightyfive`
packages the signed finite-selector trace
`fl(((+/-2^k)/16385)*16385) = +/-2^k` for `k <= 1023`.
The next genuinely new odd denominator `32769` is now closed for power-of-two
numerators: `problem2_10_denominator_thirtytwothousandsevenhundredsixtynine_eq_power_sum`
and `problem2_10_thirtytwothousandsevenhundredsixtynine_allowableDenominator`
prove `32769 = 2^15 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_thirtytwothousandsevenhundredsixtynine`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_thirtytwothousandsevenhundredsixtynine`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_thirtytwothousandsevenhundredsixtyninths_rounds_to_lower`
proves the first rounded division sends `(2^k)/32769` to
`9006924385222400 * 2^(k-68)`;
`problem2_10_ieeeDouble_div_two_pow_thirtytwothousandsevenhundredsixtynine_exact_mul_thirtytwothousandsevenhundredsixtynine_below`
proves the exact product with `32769` is
`2^k - 2^(k-60)`; the already proved
`problem2_10_ieeeDouble_two_pow_minus_one_twohundredfiftysixth_ulp_rounds_to_two_pow`
proves the final round returns `2^k` because that exact product is one 128th
of the lower ulp below `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_thirtytwothousandsevenhundredsixtyninths_times_thirtytwothousandsevenhundredsixtynine`
packages the signed finite-selector trace
`fl(((+/-2^k)/32769)*32769) = +/-2^k` for `k <= 1023`.
The next genuinely new odd denominator `65537` is now closed for power-of-two
numerators: `problem2_10_denominator_sixtyfivethousandfivehundredthirtyseven_eq_power_sum`
and `problem2_10_sixtyfivethousandfivehundredthirtyseven_allowableDenominator`
prove `65537 = 2^16 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_sixtyfivethousandfivehundredthirtyseven`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_sixtyfivethousandfivehundredthirtyseven`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_sixtyfivethousandfivehundredthirtysevenths_rounds_to_lower`
proves the first rounded division sends `(2^k)/65537` to
`9007061817884640 * 2^(k-69)`;
`problem2_10_ieeeDouble_div_two_pow_sixtyfivethousandfivehundredthirtyseven_exact_mul_sixtyfivethousandfivehundredthirtyseven_below`
proves the exact product with `65537` is
`2^k - 2^(k-64)`; the new
`problem2_10_ieeeDouble_two_pow_minus_one_fourthousandninetysixth_ulp_rounds_to_two_pow`
proves the final round returns `2^k` because that exact product is one 2048th
of the lower ulp below `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_sixtyfivethousandfivehundredthirtysevenths_times_sixtyfivethousandfivehundredthirtyseven`
packages the signed finite-selector trace
`fl(((+/-2^k)/65537)*65537) = +/-2^k` for `k <= 1023`.
The next genuinely new odd denominator `131073` is now closed for power-of-two
numerators: `problem2_10_denominator_onehundredthirtyonethousandseventythree_eq_power_sum`
and `problem2_10_onehundredthirtyonethousandseventythree_allowableDenominator`
prove `131073 = 2^17 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_onehundredthirtyonethousandseventythree`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_onehundredthirtyonethousandseventythree`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_onehundredthirtyonethousandseventythirds_rounds_to_lower`
proves the first rounded division sends `(2^k)/131073` to
`9007130535788540 * 2^(k-70)`;
`problem2_10_ieeeDouble_div_two_pow_onehundredthirtyonethousandseventythree_exact_mul_onehundredthirtyonethousandseventythree_below`
proves the exact product with `131073` is
`2^k - 2^(k-68)`; the new
`problem2_10_ieeeDouble_two_pow_minus_one_sixtythreethousandfivehundredthirtysixth_ulp_rounds_to_two_pow`
proves the final round returns `2^k` because that exact product is one
32768th of the lower ulp below `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_onehundredthirtyonethousandseventythirds_times_onehundredthirtyonethousandseventythree`
packages the signed finite-selector trace
`fl(((+/-2^k)/131073)*131073) = +/-2^k` for `k <= 1023`.
The next genuinely new odd denominator `262145` is now closed for power-of-two
numerators: `problem2_10_denominator_twohundredsixtytwothousandonehundredfortyfive_eq_power_sum`
and `problem2_10_twohundredsixtytwothousandonehundredfortyfive_allowableDenominator`
prove `262145 = 2^18 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_twohundredsixtytwothousandonehundredfortyfive`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_twohundredsixtytwothousandonehundredfortyfive`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_twohundredsixtytwothousandonehundredfortyfifths_rounds_to_upper`
proves the first rounded division sends `(2^k)/262145` to
`9007164895133696 * 2^(k-71)`;
`problem2_10_ieeeDouble_div_two_pow_twohundredsixtytwothousandonehundredfortyfive_exact_mul_twohundredsixtytwothousandonehundredfortyfive_above`
proves the exact product with `262145` is
`2^k + 2^(k-54)`; the already proved
`problem2_10_ieeeDouble_two_pow_plus_quarter_ulp_rounds_to_two_pow`
proves the final round returns `2^k` because that exact product is one quarter
of the upper ulp above `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_twohundredsixtytwothousandonehundredfortyfifths_times_twohundredsixtytwothousandonehundredfortyfive`
packages the signed finite-selector trace
`fl(((+/-2^k)/262145)*262145) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `524289` is now closed for power-of-two
numerators: `problem2_10_denominator_fivehundredtwentyfourthousandtwohundredeightynine_eq_power_sum`
and `problem2_10_fivehundredtwentyfourthousandtwohundredeightynine_allowableDenominator`
prove `524289 = 2^19 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_fivehundredtwentyfourthousandtwohundredeightynine`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_fivehundredtwentyfourthousandtwohundredeightynine`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_fivehundredtwentyfourthousandtwohundredeightyninths_rounds_to_upper`
proves the first rounded division sends `(2^k)/524289` to
`9007182074904576 * 2^(k-72)`;
`problem2_10_ieeeDouble_div_two_pow_fivehundredtwentyfourthousandtwohundredeightynine_exact_mul_fivehundredtwentyfourthousandtwohundredeightynine_above`
proves the exact product with `524289` is
`2^k + 2^(k-57)`; the new
`problem2_10_ieeeDouble_two_pow_plus_one_thirtysecond_ulp_rounds_to_two_pow`
proves the final round returns `2^k` because that exact product is one 32nd
of the upper ulp above `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_fivehundredtwentyfourthousandtwohundredeightyninths_times_fivehundredtwentyfourthousandtwohundredeightynine`
packages the signed finite-selector trace
`fl(((+/-2^k)/524289)*524289) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `1048577` is now closed for power-of-two
numerators: `problem2_10_denominator_onemillionfortyeightthousandfivehundredseventyseven_eq_power_sum`
and `problem2_10_onemillionfortyeightthousandfivehundredseventyseven_allowableDenominator`
prove `1048577 = 2^20 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_onemillionfortyeightthousandfivehundredseventyseven`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_onemillionfortyeightthousandfivehundredseventyseven`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_onemillionfortyeightthousandfivehundredseventysevenths_rounds_to_upper`
proves the first rounded division sends `(2^k)/1048577` to
`9007190664814592 * 2^(k-73)`;
`problem2_10_ieeeDouble_div_two_pow_onemillionfortyeightthousandfivehundredseventyseven_exact_mul_onemillionfortyeightthousandfivehundredseventyseven_above`
proves the exact product with `1048577` is
`2^k + 2^(k-60)`; the already proved
`problem2_10_ieeeDouble_two_pow_plus_one_twohundredfiftysixth_ulp_rounds_to_two_pow`
proves the final round returns `2^k` because that exact product is one 256th
of the upper ulp above `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_onemillionfortyeightthousandfivehundredseventysevenths_times_onemillionfortyeightthousandfivehundredseventyseven`
packages the signed finite-selector trace
`fl(((+/-2^k)/1048577)*1048577) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `2097153` is now closed for power-of-two
numerators: `problem2_10_denominator_twomillionninetyseventhousandonehundredfiftythree_eq_power_sum`
and `problem2_10_twomillionninetyseventhousandonehundredfiftythree_allowableDenominator`
prove `2097153 = 2^21 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_twomillionninetyseventhousandonehundredfiftythree`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_twomillionninetyseventhousandonehundredfiftythree`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_twomillionninetyseventhousandonehundredfiftythirds_rounds_to_upper`
proves the first rounded division sends `(2^k)/2097153` to
`9007194959775744 * 2^(k-74)`;
`problem2_10_ieeeDouble_div_two_pow_twomillionninetyseventhousandonehundredfiftythree_exact_mul_twomillionninetyseventhousandonehundredfiftythree_above`
proves the exact product with `2097153` is
`2^k + 2^(k-63)`; the new
`problem2_10_ieeeDouble_two_pow_plus_one_twothousandfortyeighth_ulp_rounds_to_two_pow`
proves the final round returns `2^k` because that exact product is one 2048th
of the upper ulp above `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_twomillionninetyseventhousandonehundredfiftythirds_times_twomillionninetyseventhousandonehundredfiftythree`
packages the signed finite-selector trace
`fl(((+/-2^k)/2097153)*2097153) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `4194305` is now closed for power-of-two
numerators: `problem2_10_denominator_fourmilliononehundredninetyfourthousandthreehundredfive_eq_power_sum`
and `problem2_10_fourmilliononehundredninetyfourthousandthreehundredfive_allowableDenominator`
prove `4194305 = 2^22 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_fourmilliononehundredninetyfourthousandthreehundredfive`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_fourmilliononehundredninetyfourthousandthreehundredfive`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_fourmilliononehundredninetyfourthousandthreehundredfifths_rounds_to_upper`
proves the first rounded division sends `(2^k)/4194305` to
`9007197107257856 * 2^(k-75)`;
`problem2_10_ieeeDouble_div_two_pow_fourmilliononehundredninetyfourthousandthreehundredfive_exact_mul_fourmilliononehundredninetyfourthousandthreehundredfive_above`
proves the exact product with `4194305` is
`2^k + 2^(k-66)`; the new
`problem2_10_ieeeDouble_two_pow_plus_one_sixteenthousandthreehundredeightyfourth_ulp_rounds_to_two_pow`
proves the final round returns `2^k` because that exact product is one
16384th of the upper ulp above `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_fourmilliononehundredninetyfourthousandthreehundredfifths_times_fourmilliononehundredninetyfourthousandthreehundredfive`
packages the signed finite-selector trace
`fl(((+/-2^k)/4194305)*4194305) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `8388609` is now closed for power-of-two
numerators:
`problem2_10_denominator_eightmillionthreehundredeightyeightthousandsixhundrednine_eq_power_sum`
and
`problem2_10_eightmillionthreehundredeightyeightthousandsixhundrednine_allowableDenominator`
prove `8388609 = 2^23 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_eightmillionthreehundredeightyeightthousandsixhundrednine`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_eightmillionthreehundredeightyeightthousandsixhundrednine`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_eightmillionthreehundredeightyeightthousandsixhundredninths_rounds_to_upper`
proves the first rounded division sends `(2^k)/8388609` to
`9007198180999296 * 2^(k-76)`;
`problem2_10_ieeeDouble_div_two_pow_eightmillionthreehundredeightyeightthousandsixhundrednine_exact_mul_eightmillionthreehundredeightyeightthousandsixhundrednine_above`
proves the exact product with `8388609` is
`2^k + 2^(k-69)`; the new
`problem2_10_ieeeDouble_two_pow_plus_one_onehundredthirtyonethousandseventysecond_ulp_rounds_to_two_pow`
proves the final round returns `2^k` because that exact product is one
131072nd of the upper ulp above `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_eightmillionthreehundredeightyeightthousandsixhundredninths_times_eightmillionthreehundredeightyeightthousandsixhundrednine`
packages the signed finite-selector trace
`fl(((+/-2^k)/8388609)*8388609) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `16777217` is now closed for
power-of-two numerators:
`problem2_10_denominator_sixteenmillionsevenhundredseventyseventhousandtwohundredseventeen_eq_power_sum`
and
`problem2_10_sixteenmillionsevenhundredseventyseventhousandtwohundredseventeen_allowableDenominator`
prove `16777217 = 2^24 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_sixteenmillionsevenhundredseventyseventhousandtwohundredseventeen`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_sixteenmillionsevenhundredseventyseventhousandtwohundredseventeen`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_sixteenmillionsevenhundredseventyseventhousandtwohundredseventeenths_rounds_to_upper`
proves the first rounded division sends `(2^k)/16777217` to
`9007198717870112 * 2^(k-77)`;
`problem2_10_ieeeDouble_div_two_pow_sixteenmillionsevenhundredseventyseventhousandtwohundredseventeen_exact_mul_sixteenmillionsevenhundredseventyseventhousandtwohundredseventeen_above`
proves the exact product with `16777217` is
`2^k + 2^(k-72)`; the new
`problem2_10_ieeeDouble_two_pow_plus_one_onemillionfortyeightthousandfivehundredseventysixth_ulp_rounds_to_two_pow`
proves the final round returns `2^k` because that exact product is one
1048576th of the upper ulp above `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_sixteenmillionsevenhundredseventyseventhousandtwohundredseventeenths_times_sixteenmillionsevenhundredseventyseventhousandtwohundredseventeen`
packages the signed finite-selector trace
`fl(((+/-2^k)/16777217)*16777217) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `33554433` is now closed for
power-of-two numerators:
`problem2_10_denominator_thirtythreemillionfivehundredfiftyfourthousandfourhundredthirtythree_eq_power_sum`
and
`problem2_10_thirtythreemillionfivehundredfiftyfourthousandfourhundredthirtythree_allowableDenominator`
prove `33554433 = 2^25 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_thirtythreemillionfivehundredfiftyfourthousandfourhundredthirtythree`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_thirtythreemillionfivehundredfiftyfourthousandfourhundredthirtythree`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_thirtythreemillionfivehundredfiftyfourthousandfourhundredthirtythirds_rounds_to_upper`
proves the first rounded division sends `(2^k)/33554433` to
`9007198986305544 * 2^(k-78)`;
`problem2_10_ieeeDouble_div_two_pow_thirtythreemillionfivehundredfiftyfourthousandfourhundredthirtythree_exact_mul_thirtythreemillionfivehundredfiftyfourthousandfourhundredthirtythree_above`
proves the exact product with `33554433` is
`2^k + 2^(k-75)`; the new
`problem2_10_ieeeDouble_two_pow_plus_one_eightmillionthreehundredeightyeightthousandsixhundredeighth_ulp_rounds_to_two_pow`
proves the final round returns `2^k` because that exact product is one
8388608th of the upper ulp above `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_thirtythreemillionfivehundredfiftyfourthousandfourhundredthirtythirds_times_thirtythreemillionfivehundredfiftyfourthousandfourhundredthirtythree`
packages the signed finite-selector trace
`fl(((+/-2^k)/33554433)*33554433) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `67108865` is now closed for
power-of-two numerators:
`problem2_10_denominator_sixtysevenmilliononehundredeightthousandeighthundredsixtyfive_eq_power_sum`
and
`problem2_10_sixtysevenmilliononehundredeightthousandeighthundredsixtyfive_allowableDenominator`
prove `67108865 = 2^26 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_sixtysevenmilliononehundredeightthousandeighthundredsixtyfive`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_sixtysevenmilliononehundredeightthousandeighthundredsixtyfive`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_sixtysevenmilliononehundredeightthousandeighthundredsixtyfifths_rounds_to_upper`
proves the first rounded division sends `(2^k)/67108865` to
`9007199120523266 * 2^(k-79)`;
`problem2_10_ieeeDouble_div_two_pow_sixtysevenmilliononehundredeightthousandeighthundredsixtyfive_exact_mul_sixtysevenmilliononehundredeightthousandeighthundredsixtyfive_above`
proves the exact product with `67108865` is
`2^k + 2^(k-78)`; the new
`problem2_10_ieeeDouble_two_pow_plus_one_sixtysevenmilliononehundredeightthousandeighthundredsixtyfourth_ulp_rounds_to_two_pow`
proves the final round returns `2^k` because that exact product is one
67108864th of the upper ulp above `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_sixtysevenmilliononehundredeightthousandeighthundredsixtyfifths_times_sixtysevenmilliononehundredeightthousandeighthundredsixtyfive`
packages the signed finite-selector trace
`fl(((+/-2^k)/67108865)*67108865) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `134217729` is now closed for
power-of-two numerators:
`problem2_10_denominator_onehundredthirtyfourmilliontwohundredseventeenthousandsevenhundredtwentynine_eq_power_sum`
and
`problem2_10_onehundredthirtyfourmilliontwohundredseventeenthousandsevenhundredtwentynine_allowableDenominator`
prove `134217729 = 2^27 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_onehundredthirtyfourmilliontwohundredseventeenthousandsevenhundredtwentynine`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_onehundredthirtyfourmilliontwohundredseventeenthousandsevenhundredtwentynine`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_onehundredthirtyfourmilliontwohundredseventeenthousandsevenhundredtwentyninths_rounds_to_lower`
proves the first rounded division sends `(2^k)/134217729` to
`9007199187632128 * 2^(k-80)`;
`problem2_10_ieeeDouble_div_two_pow_onehundredthirtyfourmilliontwohundredseventeenthousandsevenhundredtwentynine_exact_mul_onehundredthirtyfourmilliontwohundredseventeenthousandsevenhundredtwentynine_midpoint`
proves the exact product with `134217729` is the midpoint
`2^k - 2^(k-54)`; the existing
`problem2_10_ieeeDouble_midpoint_below_two_pow_rounds_to_two_pow`
proves the final tie-to-even step returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_onehundredthirtyfourmilliontwohundredseventeenthousandsevenhundredtwentyninths_times_onehundredthirtyfourmilliontwohundredseventeenthousandsevenhundredtwentynine`
packages the signed finite-selector trace
`fl(((+/-2^k)/134217729)*134217729) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `268435457` is now closed for
power-of-two numerators:
`problem2_10_denominator_twohundredsixtyeightmillionfourhundredthirtyfivethousandfourhundredfiftyseven_eq_power_sum`
and
`problem2_10_twohundredsixtyeightmillionfourhundredthirtyfivethousandfourhundredfiftyseven_allowableDenominator`
prove `268435457 = 2^28 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_twohundredsixtyeightmillionfourhundredthirtyfivethousandfourhundredfiftyseven`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_twohundredsixtyeightmillionfourhundredthirtyfivethousandfourhundredfiftyseven`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_twohundredsixtyeightmillionfourhundredthirtyfivethousandfourhundredfiftysevenths_rounds_to_lower`
proves the first rounded division sends `(2^k)/268435457` to
`9007199221186560 * 2^(k-81)`;
`problem2_10_ieeeDouble_div_two_pow_twohundredsixtyeightmillionfourhundredthirtyfivethousandfourhundredfiftyseven_exact_mul_twohundredsixtyeightmillionfourhundredthirtyfivethousandfourhundredfiftyseven_below`
proves the exact product with `268435457` is `2^k - 2^(k-56)`;
the existing
`problem2_10_ieeeDouble_two_pow_minus_one_sixteenth_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_twohundredsixtyeightmillionfourhundredthirtyfivethousandfourhundredfiftysevenths_times_twohundredsixtyeightmillionfourhundredthirtyfivethousandfourhundredfiftyseven`
packages the signed finite-selector trace
`fl(((+/-2^k)/268435457)*268435457) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `536870913` is now closed for
power-of-two numerators:
`problem2_10_denominator_fivehundredthirtysixmillioneighthundredseventythousandninehundredthirteen_eq_power_sum`
and
`problem2_10_fivehundredthirtysixmillioneighthundredseventythousandninehundredthirteen_allowableDenominator`
prove `536870913 = 2^29 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_fivehundredthirtysixmillioneighthundredseventythousandninehundredthirteen`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_fivehundredthirtysixmillioneighthundredseventythousandninehundredthirteen`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_fivehundredthirtysixmillioneighthundredseventythousandninehundredthirteenths_rounds_to_lower`
proves the first rounded division sends `(2^k)/536870913` to
`9007199237963776 * 2^(k-82)`;
`problem2_10_ieeeDouble_div_two_pow_fivehundredthirtysixmillioneighthundredseventythousandninehundredthirteen_exact_mul_fivehundredthirtysixmillioneighthundredseventythousandninehundredthirteen_below`
proves the exact product with `536870913` is `2^k - 2^(k-58)`;
the new
`problem2_10_ieeeDouble_two_pow_minus_one_sixtyfourth_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_fivehundredthirtysixmillioneighthundredseventythousandninehundredthirteenths_times_fivehundredthirtysixmillioneighthundredseventythousandninehundredthirteen`
packages the signed finite-selector trace
`fl(((+/-2^k)/536870913)*536870913) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `1073741825` is now closed for
power-of-two numerators:
`problem2_10_denominator_onebillionseventythreemillionsevenhundredfortyonethousandeighthundredtwentyfive_eq_power_sum`
and
`problem2_10_onebillionseventythreemillionsevenhundredfortyonethousandeighthundredtwentyfive_allowableDenominator`
prove `1073741825 = 2^30 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_onebillionseventythreemillionsevenhundredfortyonethousandeighthundredtwentyfive`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_onebillionseventythreemillionsevenhundredfortyonethousandeighthundredtwentyfive`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_onebillionseventythreemillionsevenhundredfortyonethousandeighthundredtwentyfifths_rounds_to_lower`
proves the first rounded division sends `(2^k)/1073741825` to
`9007199246352384 * 2^(k-83)`;
`problem2_10_ieeeDouble_div_two_pow_onebillionseventythreemillionsevenhundredfortyonethousandeighthundredtwentyfive_exact_mul_onebillionseventythreemillionsevenhundredfortyonethousandeighthundredtwentyfive_below`
proves the exact product with `1073741825` is `2^k - 2^(k-60)`;
the existing
`problem2_10_ieeeDouble_two_pow_minus_one_twohundredfiftysixth_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_onebillionseventythreemillionsevenhundredfortyonethousandeighthundredtwentyfifths_times_onebillionseventythreemillionsevenhundredfortyonethousandeighthundredtwentyfive`
packages the signed finite-selector trace
`fl(((+/-2^k)/1073741825)*1073741825) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `2147483649` is now closed for
power-of-two numerators:
`problem2_10_denominator_twobilliononehundredfortysevenmillionfourhundredeightythreethousandsixhundredfortynine_eq_power_sum`
and
`problem2_10_twobilliononehundredfortysevenmillionfourhundredeightythreethousandsixhundredfortynine_allowableDenominator`
prove `2147483649 = 2^31 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_twobilliononehundredfortysevenmillionfourhundredeightythreethousandsixhundredfortynine`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_twobilliononehundredfortysevenmillionfourhundredeightythreethousandsixhundredfortynine`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_twobilliononehundredfortysevenmillionfourhundredeightythreethousandsixhundredfortyninths_rounds_to_lower`
proves the first rounded division sends `(2^k)/2147483649` to
`9007199250546688 * 2^(k-84)`;
`problem2_10_ieeeDouble_div_two_pow_twobilliononehundredfortysevenmillionfourhundredeightythreethousandsixhundredfortynine_exact_mul_twobilliononehundredfortysevenmillionfourhundredeightythreethousandsixhundredfortynine_below`
proves the exact product with `2147483649` is `2^k - 2^(k-62)`;
the new
`problem2_10_ieeeDouble_two_pow_minus_one_onethousandtwentyfourth_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_twobilliononehundredfortysevenmillionfourhundredeightythreethousandsixhundredfortyninths_times_twobilliononehundredfortysevenmillionfourhundredeightythreethousandsixhundredfortynine`
packages the signed finite-selector trace
`fl(((+/-2^k)/2147483649)*2147483649) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `4294967297` is now closed for
power-of-two numerators:
`problem2_10_denominator_fourbilliontwohundredninetyfourmillionninehundredsixtyseventhousandtwohundredninetyseven_eq_power_sum`
and
`problem2_10_fourbilliontwohundredninetyfourmillionninehundredsixtyseventhousandtwohundredninetyseven_allowableDenominator`
prove `4294967297 = 2^32 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_fourbilliontwohundredninetyfourmillionninehundredsixtyseventhousandtwohundredninetyseven`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_fourbilliontwohundredninetyfourmillionninehundredsixtyseventhousandtwohundredninetyseven`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_fourbilliontwohundredninetyfourmillionninehundredsixtyseventhousandtwohundredninetysevenths_rounds_to_lower`
proves the first rounded division sends `(2^k)/4294967297` to
`9007199252643840 * 2^(k-85)`;
`problem2_10_ieeeDouble_div_two_pow_fourbilliontwohundredninetyfourmillionninehundredsixtyseventhousandtwohundredninetyseven_exact_mul_fourbilliontwohundredninetyfourmillionninehundredsixtyseventhousandtwohundredninetyseven_below`
proves the exact product with `4294967297` is `2^k - 2^(k-64)`;
the existing
`problem2_10_ieeeDouble_two_pow_minus_one_fourthousandninetysixth_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_fourbilliontwohundredninetyfourmillionninehundredsixtyseventhousandtwohundredninetysevenths_times_fourbilliontwohundredninetyfourmillionninehundredsixtyseventhousandtwohundredninetyseven`
packages the signed finite-selector trace
`fl(((+/-2^k)/4294967297)*4294967297) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `8589934593` is now closed for
power-of-two numerators:
`problem2_10_denominator_eightbillionfivehundredeightyninemillionninehundredthirtyfourthousandfivehundredninetythree_eq_power_sum`
and
`problem2_10_eightbillionfivehundredeightyninemillionninehundredthirtyfourthousandfivehundredninetythree_allowableDenominator`
prove `8589934593 = 2^33 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_eightbillionfivehundredeightyninemillionninehundredthirtyfourthousandfivehundredninetythree`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_eightbillionfivehundredeightyninemillionninehundredthirtyfourthousandfivehundredninetythree`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_eightbillionfivehundredeightyninemillionninehundredthirtyfourthousandfivehundredninetythirds_rounds_to_lower`
proves the first rounded division sends `(2^k)/8589934593` to
`9007199253692416 * 2^(k-86)`;
`problem2_10_ieeeDouble_div_two_pow_eightbillionfivehundredeightyninemillionninehundredthirtyfourthousandfivehundredninetythree_exact_mul_eightbillionfivehundredeightyninemillionninehundredthirtyfourthousandfivehundredninetythree_below`
proves the exact product with `8589934593` is `2^k - 2^(k-66)`;
the new
`problem2_10_ieeeDouble_two_pow_minus_one_sixteenthousandthreehundredeightyfourth_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_eightbillionfivehundredeightyninemillionninehundredthirtyfourthousandfivehundredninetythirds_times_eightbillionfivehundredeightyninemillionninehundredthirtyfourthousandfivehundredninetythree`
packages the signed finite-selector trace
`fl(((+/-2^k)/8589934593)*8589934593) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `17179869185` is now closed for
power-of-two numerators:
`problem2_10_denominator_seventeenbilliononehundredseventyninemillioneighthundredsixtyninethousandonehundredeightyfive_eq_power_sum`
and
`problem2_10_seventeenbilliononehundredseventyninemillioneighthundredsixtyninethousandonehundredeightyfive_allowableDenominator`
prove `17179869185 = 2^34 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_seventeenbilliononehundredseventyninemillioneighthundredsixtyninethousandonehundredeightyfive`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_seventeenbilliononehundredseventyninemillioneighthundredsixtyninethousandonehundredeightyfive`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_seventeenbilliononehundredseventyninemillioneighthundredsixtyninethousandonehundredeightyfifths_rounds_to_lower`
proves the first rounded division sends `(2^k)/17179869185` to
`9007199254216704 * 2^(k-87)`;
`problem2_10_ieeeDouble_div_two_pow_seventeenbilliononehundredseventyninemillioneighthundredsixtyninethousandonehundredeightyfive_exact_mul_seventeenbilliononehundredseventyninemillioneighthundredsixtyninethousandonehundredeightyfive_below`
proves the exact product with `17179869185` is `2^k - 2^(k-68)`;
the existing
`problem2_10_ieeeDouble_two_pow_minus_one_sixtythreethousandfivehundredthirtysixth_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_seventeenbilliononehundredseventyninemillioneighthundredsixtyninethousandonehundredeightyfifths_times_seventeenbilliononehundredseventyninemillioneighthundredsixtyninethousandonehundredeightyfive`
packages the signed finite-selector trace
`fl(((+/-2^k)/17179869185)*17179869185) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `34359738369` is now closed for
power-of-two numerators:
`problem2_10_denominator_thirtyfourbillionthreehundredfiftyninemillionsevenhundredthirtyeightthousandthreehundredsixtynine_eq_power_sum`
and
`problem2_10_thirtyfourbillionthreehundredfiftyninemillionsevenhundredthirtyeightthousandthreehundredsixtynine_allowableDenominator`
prove `34359738369 = 2^35 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_thirtyfourbillionthreehundredfiftyninemillionsevenhundredthirtyeightthousandthreehundredsixtynine`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_thirtyfourbillionthreehundredfiftyninemillionsevenhundredthirtyeightthousandthreehundredsixtynine`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_thirtyfourbillionthreehundredfiftyninemillionsevenhundredthirtyeightthousandthreehundredsixtyninths_rounds_to_lower`
proves the first rounded division sends `(2^k)/34359738369` to
`9007199254478848 * 2^(k-88)`;
`problem2_10_ieeeDouble_div_two_pow_thirtyfourbillionthreehundredfiftyninemillionsevenhundredthirtyeightthousandthreehundredsixtynine_exact_mul_thirtyfourbillionthreehundredfiftyninemillionsevenhundredthirtyeightthousandthreehundredsixtynine_below`
proves the exact product with `34359738369` is `2^k - 2^(k-70)`;
the new
`problem2_10_ieeeDouble_two_pow_minus_one_twohundredsixtytwothousandonehundredfortyfourth_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_thirtyfourbillionthreehundredfiftyninemillionsevenhundredthirtyeightthousandthreehundredsixtyninths_times_thirtyfourbillionthreehundredfiftyninemillionsevenhundredthirtyeightthousandthreehundredsixtynine`
packages the signed finite-selector trace
`fl(((+/-2^k)/34359738369)*34359738369) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `68719476737` is now closed for
power-of-two numerators:
`problem2_10_denominator_sixtyeightbillionsevenhundrednineteenmillionfourhundredseventysixthousandsevenhundredthirtyseven_eq_power_sum`
and
`problem2_10_sixtyeightbillionsevenhundrednineteenmillionfourhundredseventysixthousandsevenhundredthirtyseven_allowableDenominator`
prove `68719476737 = 2^36 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_sixtyeightbillionsevenhundrednineteenmillionfourhundredseventysixthousandsevenhundredthirtyseven`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_sixtyeightbillionsevenhundrednineteenmillionfourhundredseventysixthousandsevenhundredthirtyseven`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_sixtyeightbillionsevenhundrednineteenmillionfourhundredseventysixthousandsevenhundredthirtysevenths_rounds_to_lower`
proves the first rounded division sends `(2^k)/68719476737` to
`9007199254609920 * 2^(k-89)`;
`problem2_10_ieeeDouble_div_two_pow_sixtyeightbillionsevenhundrednineteenmillionfourhundredseventysixthousandsevenhundredthirtyseven_exact_mul_sixtyeightbillionsevenhundrednineteenmillionfourhundredseventysixthousandsevenhundredthirtyseven_below`
proves the exact product with `68719476737` is `2^k - 2^(k-72)`;
the new
`problem2_10_ieeeDouble_two_pow_minus_one_onemillionfortyeightthousandfivehundredseventysixth_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_sixtyeightbillionsevenhundrednineteenmillionfourhundredseventysixthousandsevenhundredthirtysevenths_times_sixtyeightbillionsevenhundrednineteenmillionfourhundredseventysixthousandsevenhundredthirtyseven`
packages the signed finite-selector trace
`fl(((+/-2^k)/68719476737)*68719476737) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `137438953473` is now closed for
power-of-two numerators:
`problem2_10_denominator_onehundredthirtysevenbillionfourhundredthirtyeightmillionninehundredfiftythreethousandfourhundredseventythree_eq_power_sum`
and
`problem2_10_onehundredthirtysevenbillionfourhundredthirtyeightmillionninehundredfiftythreethousandfourhundredseventythree_allowableDenominator`
prove `137438953473 = 2^37 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_onehundredthirtysevenbillionfourhundredthirtyeightmillionninehundredfiftythreethousandfourhundredseventythree`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_onehundredthirtysevenbillionfourhundredthirtyeightmillionninehundredfiftythreethousandfourhundredseventythree`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_onehundredthirtysevenbillionfourhundredthirtyeightmillionninehundredfiftythreethousandfourhundredseventythirds_rounds_to_lower`
proves the first rounded division sends `(2^k)/137438953473` to
`9007199254675456 * 2^(k-90)`;
`problem2_10_ieeeDouble_div_two_pow_onehundredthirtysevenbillionfourhundredthirtyeightmillionninehundredfiftythreethousandfourhundredseventythree_exact_mul_onehundredthirtysevenbillionfourhundredthirtyeightmillionninehundredfiftythreethousandfourhundredseventythree_below`
proves the exact product with `137438953473` is `2^k - 2^(k-74)`;
the new
`problem2_10_ieeeDouble_two_pow_minus_one_fourmilliononehundredninetyfourthousandthreehundredfourth_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_onehundredthirtysevenbillionfourhundredthirtyeightmillionninehundredfiftythreethousandfourhundredseventythirds_times_onehundredthirtysevenbillionfourhundredthirtyeightmillionninehundredfiftythreethousandfourhundredseventythree`
packages the signed finite-selector trace
`fl(((+/-2^k)/137438953473)*137438953473) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `274877906945` is now closed for
power-of-two numerators:
`problem2_10_denominator_twohundredseventyfourbillioneighthundredseventysevenmillionninehundredsixthousandninehundredfortyfive_eq_power_sum`
and
`problem2_10_twohundredseventyfourbillioneighthundredseventysevenmillionninehundredsixthousandninehundredfortyfive_allowableDenominator`
prove `274877906945 = 2^38 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_twohundredseventyfourbillioneighthundredseventysevenmillionninehundredsixthousandninehundredfortyfive`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_twohundredseventyfourbillioneighthundredseventysevenmillionninehundredsixthousandninehundredfortyfive`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_twohundredseventyfourbillioneighthundredseventysevenmillionninehundredsixthousandninehundredfortyfifths_rounds_to_lower`
proves the first rounded division sends `(2^k)/274877906945` to
`9007199254708224 * 2^(k-91)`;
`problem2_10_ieeeDouble_div_two_pow_twohundredseventyfourbillioneighthundredseventysevenmillionninehundredsixthousandninehundredfortyfive_exact_mul_twohundredseventyfourbillioneighthundredseventysevenmillionninehundredsixthousandninehundredfortyfive_below`
proves the exact product with `274877906945` is `2^k - 2^(k-76)`;
the new
`problem2_10_ieeeDouble_two_pow_minus_one_sixteenmillionsevenhundredseventyseventhousandtwohundredsixteenth_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_twohundredseventyfourbillioneighthundredseventysevenmillionninehundredsixthousandninehundredfortyfifths_times_twohundredseventyfourbillioneighthundredseventysevenmillionninehundredsixthousandninehundredfortyfive`
packages the signed finite-selector trace
`fl(((+/-2^k)/274877906945)*274877906945) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `549755813889` is now closed for
power-of-two numerators:
`problem2_10_denominator_fivehundredfortyninebillionsevenhundredfiftyfivemillioneighthundredthirteenthousandeighthundredeightynine_eq_power_sum`
and
`problem2_10_fivehundredfortyninebillionsevenhundredfiftyfivemillioneighthundredthirteenthousandeighthundredeightynine_allowableDenominator`
prove `549755813889 = 2^39 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_fivehundredfortyninebillionsevenhundredfiftyfivemillioneighthundredthirteenthousandeighthundredeightynine`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_fivehundredfortyninebillionsevenhundredfiftyfivemillioneighthundredthirteenthousandeighthundredeightynine`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_fivehundredfortyninebillionsevenhundredfiftyfivemillioneighthundredthirteenthousandeighthundredeightyninths_rounds_to_lower`
proves the first rounded division sends `(2^k)/549755813889` to
`9007199254724608 * 2^(k-92)`;
`problem2_10_ieeeDouble_div_two_pow_fivehundredfortyninebillionsevenhundredfiftyfivemillioneighthundredthirteenthousandeighthundredeightynine_exact_mul_fivehundredfortyninebillionsevenhundredfiftyfivemillioneighthundredthirteenthousandeighthundredeightynine_below`
proves the exact product with `549755813889` is `2^k - 2^(k-78)`;
the new
`problem2_10_ieeeDouble_two_pow_minus_one_sixtysevenmilliononehundredeightthousandsixtyfourth_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_fivehundredfortyninebillionsevenhundredfiftyfivemillioneighthundredthirteenthousandeighthundredeightyninths_times_fivehundredfortyninebillionsevenhundredfiftyfivemillioneighthundredthirteenthousandeighthundredeightynine`
packages the signed finite-selector trace
`fl(((+/-2^k)/549755813889)*549755813889) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `1099511627777` is now closed for
power-of-two numerators:
`problem2_10_denominator_two_pow_forty_plus_one_eq_power_sum`
and
`problem2_10_two_pow_forty_plus_one_allowableDenominator`
prove `1099511627777 = 2^40 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_forty_plus_one_denominator_rounds_to_lower`
proves the first rounded division sends `(2^k)/1099511627777` to
`9007199254732800 * 2^(k-93)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_forty_plus_one_exact_mul_two_pow_forty_plus_one_below`
proves the exact product with `1099511627777` is `2^k - 2^(k-80)`;
the new
`problem2_10_ieeeDouble_two_pow_minus_one_twohundredsixtyeightmillionfourhundredthirtyfivethousandfourhundredfiftysixth_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_forty_plus_one_denominator_times_two_pow_forty_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/1099511627777)*1099511627777) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `2199023255553` is now closed for
power-of-two numerators:
`problem2_10_denominator_two_pow_forty_one_plus_one_eq_power_sum`
and
`problem2_10_two_pow_forty_one_plus_one_allowableDenominator`
prove `2199023255553 = 2^41 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_one_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_one_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_forty_one_plus_one_denominator_rounds_to_lower`
proves the first rounded division sends `(2^k)/2199023255553` to
`9007199254736896 * 2^(k-94)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_forty_one_plus_one_exact_mul_two_pow_forty_one_plus_one_below`
proves the exact product with `2199023255553` is `2^k - 2^(k-82)`;
the new
`problem2_10_ieeeDouble_two_pow_minus_one_two_pow_thirty_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_forty_one_plus_one_denominator_times_two_pow_forty_one_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/2199023255553)*2199023255553) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `4398046511105` is now closed for
power-of-two numerators:
`problem2_10_denominator_two_pow_forty_two_plus_one_eq_power_sum`
and
`problem2_10_two_pow_forty_two_plus_one_allowableDenominator`
prove `4398046511105 = 2^42 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_two_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_two_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_forty_two_plus_one_denominator_rounds_to_lower`
proves the first rounded division sends `(2^k)/4398046511105` to
`9007199254738944 * 2^(k-95)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_forty_two_plus_one_exact_mul_two_pow_forty_two_plus_one_below`
proves the exact product with `4398046511105` is `2^k - 2^(k-84)`;
the new
`problem2_10_ieeeDouble_two_pow_minus_one_two_pow_thirty_two_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_forty_two_plus_one_denominator_times_two_pow_forty_two_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/4398046511105)*4398046511105) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `8796093022209` is now closed for
power-of-two numerators:
`problem2_10_denominator_two_pow_forty_three_plus_one_eq_power_sum`
and
`problem2_10_two_pow_forty_three_plus_one_allowableDenominator`
prove `8796093022209 = 2^43 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_three_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_three_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_forty_three_plus_one_denominator_rounds_to_lower`
proves the first rounded division sends `(2^k)/8796093022209` to
`9007199254739968 * 2^(k-96)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_forty_three_plus_one_exact_mul_two_pow_forty_three_plus_one_below`
proves the exact product with `8796093022209` is `2^k - 2^(k-86)`;
the new
`problem2_10_ieeeDouble_two_pow_minus_one_two_pow_thirty_four_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_forty_three_plus_one_denominator_times_two_pow_forty_three_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/8796093022209)*8796093022209) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `17592186044417` is now closed for
power-of-two numerators:
`problem2_10_denominator_two_pow_forty_four_plus_one_eq_power_sum`
and
`problem2_10_two_pow_forty_four_plus_one_allowableDenominator`
prove `17592186044417 = 2^44 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_four_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_four_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_forty_four_plus_one_denominator_rounds_to_lower`
proves the first rounded division sends `(2^k)/17592186044417` to
`9007199254740480 * 2^(k-97)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_forty_four_plus_one_exact_mul_two_pow_forty_four_plus_one_below`
proves the exact product with `17592186044417` is `2^k - 2^(k-88)`;
the new
`problem2_10_ieeeDouble_two_pow_minus_one_two_pow_thirty_six_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_forty_four_plus_one_denominator_times_two_pow_forty_four_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/17592186044417)*17592186044417) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `35184372088833` is now closed for
power-of-two numerators:
`problem2_10_denominator_two_pow_forty_five_plus_one_eq_power_sum`
and
`problem2_10_two_pow_forty_five_plus_one_allowableDenominator`
prove `35184372088833 = 2^45 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_five_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_five_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_forty_five_plus_one_denominator_rounds_to_lower`
proves the first rounded division sends `(2^k)/35184372088833` to
`9007199254740736 * 2^(k-98)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_forty_five_plus_one_exact_mul_two_pow_forty_five_plus_one_below`
proves the exact product with `35184372088833` is `2^k - 2^(k-90)`;
the new
`problem2_10_ieeeDouble_two_pow_minus_one_two_pow_thirty_eight_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_forty_five_plus_one_denominator_times_two_pow_forty_five_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/35184372088833)*35184372088833) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `70368744177665` is now closed for
power-of-two numerators:
`problem2_10_denominator_two_pow_forty_six_plus_one_eq_power_sum`
and
`problem2_10_two_pow_forty_six_plus_one_allowableDenominator`
prove `70368744177665 = 2^46 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_six_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_six_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_forty_six_plus_one_denominator_rounds_to_lower`
proves the first rounded division sends `(2^k)/70368744177665` to
`9007199254740864 * 2^(k-99)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_forty_six_plus_one_exact_mul_two_pow_forty_six_plus_one_below`
proves the exact product with `70368744177665` is `2^k - 2^(k-92)`;
the new
`problem2_10_ieeeDouble_two_pow_minus_one_two_pow_forty_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_forty_six_plus_one_denominator_times_two_pow_forty_six_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/70368744177665)*70368744177665) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `140737488355329` is now closed for
power-of-two numerators:
`problem2_10_denominator_two_pow_forty_seven_plus_one_eq_power_sum`
and
`problem2_10_two_pow_forty_seven_plus_one_allowableDenominator`
prove `140737488355329 = 2^47 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_seven_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_seven_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_forty_seven_plus_one_denominator_rounds_to_lower`
proves the first rounded division sends `(2^k)/140737488355329` to
`9007199254740928 * 2^(k-100)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_forty_seven_plus_one_exact_mul_two_pow_forty_seven_plus_one_below`
proves the exact product with `140737488355329` is `2^k - 2^(k-94)`;
the new
`problem2_10_ieeeDouble_two_pow_minus_one_two_pow_forty_two_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_forty_seven_plus_one_denominator_times_two_pow_forty_seven_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/140737488355329)*140737488355329) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `281474976710657` is now closed for
power-of-two numerators:
`problem2_10_denominator_two_pow_forty_eight_plus_one_eq_power_sum`
and
`problem2_10_two_pow_forty_eight_plus_one_allowableDenominator`
prove `281474976710657 = 2^48 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_eight_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_eight_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_forty_eight_plus_one_denominator_rounds_to_lower`
proves the first rounded division sends `(2^k)/281474976710657` to
`9007199254740960 * 2^(k-101)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_forty_eight_plus_one_exact_mul_two_pow_forty_eight_plus_one_below`
proves the exact product with `281474976710657` is `2^k - 2^(k-96)`;
the new
`problem2_10_ieeeDouble_two_pow_minus_one_two_pow_forty_four_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_forty_eight_plus_one_denominator_times_two_pow_forty_eight_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/281474976710657)*281474976710657) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `562949953421313` is now closed for
power-of-two numerators:
`problem2_10_denominator_two_pow_forty_nine_plus_one_eq_power_sum`
and
`problem2_10_two_pow_forty_nine_plus_one_allowableDenominator`
prove `562949953421313 = 2^49 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_nine_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_nine_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_forty_nine_plus_one_denominator_rounds_to_lower`
proves the first rounded division sends `(2^k)/562949953421313` to
`9007199254740976 * 2^(k-102)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_forty_nine_plus_one_exact_mul_two_pow_forty_nine_plus_one_below`
proves the exact product with `562949953421313` is `2^k - 2^(k-98)`;
the new
`problem2_10_ieeeDouble_two_pow_minus_one_two_pow_forty_six_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_forty_nine_plus_one_denominator_times_two_pow_forty_nine_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/562949953421313)*562949953421313) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `1125899906842625` is now closed for
power-of-two numerators:
`problem2_10_denominator_two_pow_fifty_plus_one_eq_power_sum`
and
`problem2_10_two_pow_fifty_plus_one_allowableDenominator`
prove `1125899906842625 = 2^50 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_fifty_plus_one_denominator_rounds_to_lower`
proves the first rounded division sends `(2^k)/1125899906842625` to
`9007199254740984 * 2^(k-103)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_fifty_plus_one_exact_mul_two_pow_fifty_plus_one_below`
proves the exact product with `1125899906842625` is `2^k - 2^(k-100)`;
the new
`problem2_10_ieeeDouble_two_pow_minus_one_two_pow_forty_eight_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_fifty_plus_one_denominator_times_two_pow_fifty_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/1125899906842625)*1125899906842625) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `2251799813685249` is now closed for
power-of-two numerators:
`problem2_10_denominator_two_pow_fifty_one_plus_one_eq_power_sum`
and
`problem2_10_two_pow_fifty_one_plus_one_allowableDenominator`
prove `2251799813685249 = 2^51 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_one_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_one_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_fifty_one_plus_one_denominator_rounds_to_lower`
proves the first rounded division sends `(2^k)/2251799813685249` to
`9007199254740988 * 2^(k-104)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_fifty_one_plus_one_exact_mul_two_pow_fifty_one_plus_one_below`
proves the exact product with `2251799813685249` is `2^k - 2^(k-102)`;
the new
`problem2_10_ieeeDouble_two_pow_minus_one_two_pow_fifty_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_fifty_one_plus_one_denominator_times_two_pow_fifty_one_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/2251799813685249)*2251799813685249) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `4503599627370497` is now closed for
power-of-two numerators:
`problem2_10_denominator_two_pow_fifty_two_plus_one_eq_power_sum`
and
`problem2_10_two_pow_fifty_two_plus_one_allowableDenominator`
prove `4503599627370497 = 2^52 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_two_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_two_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_fifty_two_plus_one_denominator_rounds_to_lower`
proves the first rounded division sends `(2^k)/4503599627370497` to
`9007199254740990 * 2^(k-105)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_fifty_two_plus_one_exact_mul_two_pow_fifty_two_plus_one_below`
proves the exact product with `4503599627370497` is `2^k - 2^(k-104)`;
the new
`problem2_10_ieeeDouble_two_pow_minus_one_two_pow_fifty_two_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_fifty_two_plus_one_denominator_times_two_pow_fifty_two_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/4503599627370497)*4503599627370497) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `9007199254740993` is now closed for
power-of-two numerators:
`problem2_10_denominator_two_pow_fifty_three_plus_one_eq_power_sum`
and
`problem2_10_two_pow_fifty_three_plus_one_allowableDenominator`
prove `9007199254740993 = 2^53 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_three_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_three_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_fifty_three_plus_one_denominator_rounds_to_lower`
proves the first rounded division sends `(2^k)/9007199254740993` to
`9007199254740991 * 2^(k-106)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_fifty_three_plus_one_exact_mul_two_pow_fifty_three_plus_one_below`
proves the exact product with `9007199254740993` is `2^k - 2^(k-106)`;
the new
`problem2_10_ieeeDouble_two_pow_minus_one_two_pow_fifty_four_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_fifty_three_plus_one_denominator_times_two_pow_fifty_three_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/9007199254740993)*9007199254740993) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `18014398509481985` is now closed for
power-of-two numerators:
`problem2_10_denominator_two_pow_fifty_four_plus_one_eq_power_sum`
and
`problem2_10_two_pow_fifty_four_plus_one_allowableDenominator`
prove `18014398509481985 = 2^54 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_four_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_four_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_fifty_four_plus_one_denominator_rounds_to_upper`
proves the first rounded division sends `(2^k)/18014398509481985` to
`9007199254740992 * 2^(k-107)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_fifty_four_plus_one_exact_mul_two_pow_fifty_four_plus_one_above`
proves the exact product with `18014398509481985` is `2^k + 2^(k-54)`;
the existing
`problem2_10_ieeeDouble_two_pow_plus_quarter_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_fifty_four_plus_one_denominator_times_two_pow_fifty_four_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/18014398509481985)*18014398509481985) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `36028797018963969` is now closed for
power-of-two numerators:
`problem2_10_denominator_two_pow_fifty_five_plus_one_eq_power_sum`
and
`problem2_10_two_pow_fifty_five_plus_one_allowableDenominator`
prove `36028797018963969 = 2^55 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_five_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_five_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_fifty_five_plus_one_denominator_rounds_to_upper`
proves the first rounded division sends `(2^k)/36028797018963969` to
`9007199254740992 * 2^(k-108)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_fifty_five_plus_one_exact_mul_two_pow_fifty_five_plus_one_above`
proves the exact product with `36028797018963969` is `2^k + 2^(k-55)`;
the existing
`problem2_10_ieeeDouble_two_pow_plus_one_eighth_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_fifty_five_plus_one_denominator_times_two_pow_fifty_five_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/36028797018963969)*36028797018963969) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `72057594037927937` is now closed for
power-of-two numerators:
`problem2_10_denominator_two_pow_fifty_six_plus_one_eq_power_sum`
and
`problem2_10_two_pow_fifty_six_plus_one_allowableDenominator`
prove `72057594037927937 = 2^56 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_six_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_six_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_fifty_six_plus_one_denominator_rounds_to_upper`
proves the first rounded division sends `(2^k)/72057594037927937` to
`9007199254740992 * 2^(k-109)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_fifty_six_plus_one_exact_mul_two_pow_fifty_six_plus_one_above`
proves the exact product with `72057594037927937` is `2^k + 2^(k-56)`;
the existing
`problem2_10_ieeeDouble_two_pow_plus_one_sixteenth_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_fifty_six_plus_one_denominator_times_two_pow_fifty_six_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/72057594037927937)*72057594037927937) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `144115188075855873` is now closed for
power-of-two numerators:
`problem2_10_denominator_two_pow_fifty_seven_plus_one_eq_power_sum`
and
`problem2_10_two_pow_fifty_seven_plus_one_allowableDenominator`
prove `144115188075855873 = 2^57 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_seven_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_seven_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_fifty_seven_plus_one_denominator_rounds_to_upper`
proves the first rounded division sends `(2^k)/144115188075855873` to
`9007199254740992 * 2^(k-110)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_fifty_seven_plus_one_exact_mul_two_pow_fifty_seven_plus_one_above`
proves the exact product with `144115188075855873` is `2^k + 2^(k-57)`;
the existing
`problem2_10_ieeeDouble_two_pow_plus_one_thirtysecond_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_fifty_seven_plus_one_denominator_times_two_pow_fifty_seven_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/144115188075855873)*144115188075855873) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `288230376151711745` is now closed for
power-of-two numerators:
`problem2_10_denominator_two_pow_fifty_eight_plus_one_eq_power_sum`
and
`problem2_10_two_pow_fifty_eight_plus_one_allowableDenominator`
prove `288230376151711745 = 2^58 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_eight_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_eight_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_fifty_eight_plus_one_denominator_rounds_to_upper`
proves the first rounded division sends `(2^k)/288230376151711745` to
`9007199254740992 * 2^(k-111)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_fifty_eight_plus_one_exact_mul_two_pow_fifty_eight_plus_one_above`
proves the exact product with `288230376151711745` is `2^k + 2^(k-58)`;
the new
`problem2_10_ieeeDouble_two_pow_plus_one_sixtyfourth_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_fifty_eight_plus_one_denominator_times_two_pow_fifty_eight_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/288230376151711745)*288230376151711745) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `576460752303423489` is now closed for
power-of-two numerators:
`problem2_10_denominator_two_pow_fifty_nine_plus_one_eq_power_sum`
and
`problem2_10_two_pow_fifty_nine_plus_one_allowableDenominator`
prove `576460752303423489 = 2^59 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_nine_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_nine_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_fifty_nine_plus_one_denominator_rounds_to_upper`
proves the first rounded division sends `(2^k)/576460752303423489` to
`9007199254740992 * 2^(k-112)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_fifty_nine_plus_one_exact_mul_two_pow_fifty_nine_plus_one_above`
proves the exact product with `576460752303423489` is `2^k + 2^(k-59)`;
the new
`problem2_10_ieeeDouble_two_pow_plus_one_onehundredtwentyeighth_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_fifty_nine_plus_one_denominator_times_two_pow_fifty_nine_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/576460752303423489)*576460752303423489) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `1152921504606846977` is now closed for
power-of-two numerators:
`problem2_10_denominator_two_pow_sixty_plus_one_eq_power_sum`
and
`problem2_10_two_pow_sixty_plus_one_allowableDenominator`
prove `1152921504606846977 = 2^60 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_sixty_plus_one_denominator_rounds_to_upper`
proves the first rounded division sends `(2^k)/1152921504606846977` to
`9007199254740992 * 2^(k-113)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_sixty_plus_one_exact_mul_two_pow_sixty_plus_one_above`
proves the exact product with `1152921504606846977` is `2^k + 2^(k-60)`;
the existing
`problem2_10_ieeeDouble_two_pow_plus_one_twohundredfiftysixth_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_sixty_plus_one_denominator_times_two_pow_sixty_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/1152921504606846977)*1152921504606846977) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `2305843009213693953` is now closed for
power-of-two numerators:
`problem2_10_denominator_two_pow_sixty_one_plus_one_eq_power_sum`
and
`problem2_10_two_pow_sixty_one_plus_one_allowableDenominator`
prove `2305843009213693953 = 2^61 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_one_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_one_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_sixty_one_plus_one_denominator_rounds_to_upper`
proves the first rounded division sends `(2^k)/2305843009213693953` to
`9007199254740992 * 2^(k-114)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_sixty_one_plus_one_exact_mul_two_pow_sixty_one_plus_one_above`
proves the exact product with `2305843009213693953` is `2^k + 2^(k-61)`;
the new
`problem2_10_ieeeDouble_two_pow_plus_one_fivehundredtwelfth_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_sixty_one_plus_one_denominator_times_two_pow_sixty_one_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/2305843009213693953)*2305843009213693953) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `4611686018427387905` is now closed for
power-of-two numerators:
`problem2_10_denominator_two_pow_sixty_two_plus_one_eq_power_sum`
and
`problem2_10_two_pow_sixty_two_plus_one_allowableDenominator`
prove `4611686018427387905 = 2^62 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_two_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_two_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_sixty_two_plus_one_denominator_rounds_to_upper`
proves the first rounded division sends `(2^k)/4611686018427387905` to
`9007199254740992 * 2^(k-115)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_sixty_two_plus_one_exact_mul_two_pow_sixty_two_plus_one_above`
proves the exact product with `4611686018427387905` is `2^k + 2^(k-62)`;
the new
`problem2_10_ieeeDouble_two_pow_plus_one_onethousandtwentyfourth_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_sixty_two_plus_one_denominator_times_two_pow_sixty_two_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/4611686018427387905)*4611686018427387905) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `9223372036854775809` is now closed for
power-of-two numerators:
`problem2_10_denominator_two_pow_sixty_three_plus_one_eq_power_sum`
and
`problem2_10_two_pow_sixty_three_plus_one_allowableDenominator`
prove `9223372036854775809 = 2^63 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_three_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_three_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_sixty_three_plus_one_denominator_rounds_to_upper`
proves the first rounded division sends `(2^k)/9223372036854775809` to
`9007199254740992 * 2^(k-116)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_sixty_three_plus_one_exact_mul_two_pow_sixty_three_plus_one_above`
proves the exact product with `9223372036854775809` is `2^k + 2^(k-63)`;
the existing
`problem2_10_ieeeDouble_two_pow_plus_one_twothousandfortyeighth_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_sixty_three_plus_one_denominator_times_two_pow_sixty_three_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/9223372036854775809)*9223372036854775809) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `18446744073709551617` is now closed for
power-of-two numerators:
`problem2_10_denominator_two_pow_sixty_four_plus_one_eq_power_sum`
and
`problem2_10_two_pow_sixty_four_plus_one_allowableDenominator`
prove `18446744073709551617 = 2^64 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_four_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_four_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_sixty_four_plus_one_denominator_rounds_to_upper`
proves the first rounded division sends `(2^k)/18446744073709551617` to
`9007199254740992 * 2^(k-117)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_sixty_four_plus_one_exact_mul_two_pow_sixty_four_plus_one_above`
proves the exact product with `18446744073709551617` is `2^k + 2^(k-64)`;
the new
`problem2_10_ieeeDouble_two_pow_plus_one_fourthousandninetysixth_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_sixty_four_plus_one_denominator_times_two_pow_sixty_four_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/18446744073709551617)*18446744073709551617) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `36893488147419103233` is now closed for
power-of-two numerators:
`problem2_10_denominator_two_pow_sixty_five_plus_one_eq_power_sum`
and
`problem2_10_two_pow_sixty_five_plus_one_allowableDenominator`
prove `36893488147419103233 = 2^65 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_five_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_five_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_sixty_five_plus_one_denominator_rounds_to_upper`
proves the first rounded division sends `(2^k)/36893488147419103233` to
`9007199254740992 * 2^(k-118)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_sixty_five_plus_one_exact_mul_two_pow_sixty_five_plus_one_above`
proves the exact product with `36893488147419103233` is `2^k + 2^(k-65)`;
the existing
`problem2_10_ieeeDouble_two_pow_plus_one_eightthousandonehundredninetysecond_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_sixty_five_plus_one_denominator_times_two_pow_sixty_five_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/36893488147419103233)*36893488147419103233) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `73786976294838206465` is now closed for
power-of-two numerators:
`problem2_10_denominator_two_pow_sixty_six_plus_one_eq_power_sum`
and
`problem2_10_two_pow_sixty_six_plus_one_allowableDenominator`
prove `73786976294838206465 = 2^66 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_six_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_six_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_sixty_six_plus_one_denominator_rounds_to_upper`
proves the first rounded division sends `(2^k)/73786976294838206465` to
`9007199254740992 * 2^(k-119)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_sixty_six_plus_one_exact_mul_two_pow_sixty_six_plus_one_above`
proves the exact product with `73786976294838206465` is `2^k + 2^(k-66)`;
the existing
`problem2_10_ieeeDouble_two_pow_plus_one_sixteenthousandthreehundredeightyfourth_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_sixty_six_plus_one_denominator_times_two_pow_sixty_six_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/73786976294838206465)*73786976294838206465) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `147573952589676412929` is now closed
for power-of-two numerators:
`problem2_10_denominator_two_pow_sixty_seven_plus_one_eq_power_sum`
and
`problem2_10_two_pow_sixty_seven_plus_one_allowableDenominator`
prove `147573952589676412929 = 2^67 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_seven_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_seven_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_sixty_seven_plus_one_denominator_rounds_to_upper`
proves the first rounded division sends `(2^k)/147573952589676412929` to
`9007199254740992 * 2^(k-120)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_sixty_seven_plus_one_exact_mul_two_pow_sixty_seven_plus_one_above`
proves the exact product with `147573952589676412929` is `2^k + 2^(k-67)`;
the new
`problem2_10_ieeeDouble_two_pow_plus_one_thirtytwothousandsevenhundredsixtyeighth_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_sixty_seven_plus_one_denominator_times_two_pow_sixty_seven_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/147573952589676412929)*147573952589676412929) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `295147905179352825857` is now closed
for power-of-two numerators:
`problem2_10_denominator_two_pow_sixty_eight_plus_one_eq_power_sum`
and
`problem2_10_two_pow_sixty_eight_plus_one_allowableDenominator`
prove `295147905179352825857 = 2^68 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_eight_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_eight_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_sixty_eight_plus_one_denominator_rounds_to_upper`
proves the first rounded division sends `(2^k)/295147905179352825857` to
`9007199254740992 * 2^(k-121)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_sixty_eight_plus_one_exact_mul_two_pow_sixty_eight_plus_one_above`
proves the exact product with `295147905179352825857` is `2^k + 2^(k-68)`;
the new
`problem2_10_ieeeDouble_two_pow_plus_one_sixtyfivethousandfivehundredthirtysixth_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_sixty_eight_plus_one_denominator_times_two_pow_sixty_eight_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/295147905179352825857)*295147905179352825857) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `590295810358705651713` is now closed
for power-of-two numerators:
`problem2_10_denominator_two_pow_sixty_nine_plus_one_eq_power_sum`
and
`problem2_10_two_pow_sixty_nine_plus_one_allowableDenominator`
prove `590295810358705651713 = 2^69 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_nine_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_nine_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_sixty_nine_plus_one_denominator_rounds_to_upper`
proves the first rounded division sends `(2^k)/590295810358705651713` to
`9007199254740992 * 2^(k-122)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_sixty_nine_plus_one_exact_mul_two_pow_sixty_nine_plus_one_above`
proves the exact product with `590295810358705651713` is `2^k + 2^(k-69)`;
the existing
`problem2_10_ieeeDouble_two_pow_plus_one_onehundredthirtyonethousandseventysecond_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_sixty_nine_plus_one_denominator_times_two_pow_sixty_nine_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/590295810358705651713)*590295810358705651713) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `1180591620717411303425` is now closed
for power-of-two numerators:
`problem2_10_denominator_two_pow_seventy_plus_one_eq_power_sum`
and
`problem2_10_two_pow_seventy_plus_one_allowableDenominator`
prove `1180591620717411303425 = 2^70 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_seventy_plus_one_denominator_rounds_to_upper`
proves the first rounded division sends `(2^k)/1180591620717411303425` to
`9007199254740992 * 2^(k-123)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_seventy_plus_one_exact_mul_two_pow_seventy_plus_one_above`
proves the exact product with `1180591620717411303425` is `2^k + 2^(k-70)`;
the new
`problem2_10_ieeeDouble_two_pow_plus_one_twohundredsixtytwothousandonehundredfortyfourth_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_seventy_plus_one_denominator_times_two_pow_seventy_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/1180591620717411303425)*1180591620717411303425) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `2361183241434822606849` is now closed
for power-of-two numerators:
`problem2_10_denominator_two_pow_seventy_one_plus_one_eq_power_sum`
and
`problem2_10_two_pow_seventy_one_plus_one_allowableDenominator`
prove `2361183241434822606849 = 2^71 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_one_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_one_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_seventy_one_plus_one_denominator_rounds_to_upper`
proves the first rounded division sends `(2^k)/2361183241434822606849` to
`9007199254740992 * 2^(k-124)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_seventy_one_plus_one_exact_mul_two_pow_seventy_one_plus_one_above`
proves the exact product with `2361183241434822606849` is `2^k + 2^(k-71)`;
the new
`problem2_10_ieeeDouble_two_pow_plus_one_fivehundredtwentyfourthousandtwohundredeightyeighth_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_seventy_one_plus_one_denominator_times_two_pow_seventy_one_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/2361183241434822606849)*2361183241434822606849) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `4722366482869645213697` is now closed
for power-of-two numerators:
`problem2_10_denominator_two_pow_seventy_two_plus_one_eq_power_sum`
and
`problem2_10_two_pow_seventy_two_plus_one_allowableDenominator`
prove `4722366482869645213697 = 2^72 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_two_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_two_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_seventy_two_plus_one_denominator_rounds_to_upper`
proves the first rounded division sends `(2^k)/4722366482869645213697` to
`9007199254740992 * 2^(k-125)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_seventy_two_plus_one_exact_mul_two_pow_seventy_two_plus_one_above`
proves the exact product with `4722366482869645213697` is `2^k + 2^(k-72)`;
the existing
`problem2_10_ieeeDouble_two_pow_plus_one_onemillionfortyeightthousandfivehundredseventysixth_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_seventy_two_plus_one_denominator_times_two_pow_seventy_two_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/4722366482869645213697)*4722366482869645213697) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `9444732965739290427393` is now closed
for power-of-two numerators:
`problem2_10_denominator_two_pow_seventy_three_plus_one_eq_power_sum`
and
`problem2_10_two_pow_seventy_three_plus_one_allowableDenominator`
prove `9444732965739290427393 = 2^73 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_three_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_three_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_seventy_three_plus_one_denominator_rounds_to_upper`
proves the first rounded division sends `(2^k)/9444732965739290427393` to
`9007199254740992 * 2^(k-126)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_seventy_three_plus_one_exact_mul_two_pow_seventy_three_plus_one_above`
proves the exact product with `9444732965739290427393` is `2^k + 2^(k-73)`;
the new
`problem2_10_ieeeDouble_two_pow_plus_one_twomillionninetyseventhousandonehundredfiftysecond_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_seventy_three_plus_one_denominator_times_two_pow_seventy_three_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/9444732965739290427393)*9444732965739290427393) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `18889465931478580854785` is now closed
for power-of-two numerators:
`problem2_10_denominator_two_pow_seventy_four_plus_one_eq_power_sum`
and
`problem2_10_two_pow_seventy_four_plus_one_allowableDenominator`
prove `18889465931478580854785 = 2^74 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_four_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_four_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_seventy_four_plus_one_denominator_rounds_to_upper`
proves the first rounded division sends `(2^k)/18889465931478580854785` to
`9007199254740992 * 2^(k-127)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_seventy_four_plus_one_exact_mul_two_pow_seventy_four_plus_one_above`
proves the exact product with `18889465931478580854785` is `2^k + 2^(k-74)`;
the new
`problem2_10_ieeeDouble_two_pow_plus_one_fourmilliononehundredninetyfourthousandthreehundredfourth_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_seventy_four_plus_one_denominator_times_two_pow_seventy_four_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/18889465931478580854785)*18889465931478580854785) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `37778931862957161709569` is now closed
for power-of-two numerators:
`problem2_10_denominator_two_pow_seventy_five_plus_one_eq_power_sum`
and
`problem2_10_two_pow_seventy_five_plus_one_allowableDenominator`
prove `37778931862957161709569 = 2^75 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_five_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_five_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_seventy_five_plus_one_denominator_rounds_to_upper`
proves the first rounded division sends `(2^k)/37778931862957161709569` to
`9007199254740992 * 2^(k-128)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_seventy_five_plus_one_exact_mul_two_pow_seventy_five_plus_one_above`
proves the exact product with `37778931862957161709569` is `2^k + 2^(k-75)`;
the existing
`problem2_10_ieeeDouble_two_pow_plus_one_eightmillionthreehundredeightyeightthousandsixhundredeighth_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_seventy_five_plus_one_denominator_times_two_pow_seventy_five_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/37778931862957161709569)*37778931862957161709569) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `75557863725914323419137` is now closed
for power-of-two numerators:
`problem2_10_denominator_two_pow_seventy_six_plus_one_eq_power_sum`
and
`problem2_10_two_pow_seventy_six_plus_one_allowableDenominator`
prove `75557863725914323419137 = 2^76 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_six_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_six_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_seventy_six_plus_one_denominator_rounds_to_upper`
proves the first rounded division sends `(2^k)/75557863725914323419137` to
`9007199254740992 * 2^(k-129)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_seventy_six_plus_one_exact_mul_two_pow_seventy_six_plus_one_above`
proves the exact product with `75557863725914323419137` is `2^k + 2^(k-76)`;
the new
`problem2_10_ieeeDouble_two_pow_plus_one_sixteenmillionsevenhundredseventyseventhousandtwohundredsixteenth_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_seventy_six_plus_one_denominator_times_two_pow_seventy_six_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/75557863725914323419137)*75557863725914323419137) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `151115727451828646838273` is now closed
for power-of-two numerators:
`problem2_10_denominator_two_pow_seventy_seven_plus_one_eq_power_sum`
and
`problem2_10_two_pow_seventy_seven_plus_one_allowableDenominator`
prove `151115727451828646838273 = 2^77 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_seven_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_seven_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_seventy_seven_plus_one_denominator_rounds_to_upper`
proves the first rounded division sends `(2^k)/151115727451828646838273` to
`9007199254740992 * 2^(k-130)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_seventy_seven_plus_one_exact_mul_two_pow_seventy_seven_plus_one_above`
proves the exact product with `151115727451828646838273` is `2^k + 2^(k-77)`;
the new
`problem2_10_ieeeDouble_two_pow_plus_one_thirtythreemillionfivehundredfiftyfourthousandfourhundredthirtysecond_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_seventy_seven_plus_one_denominator_times_two_pow_seventy_seven_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/151115727451828646838273)*151115727451828646838273) = +/-2^k` for `k <= 1022`.
The next genuinely new odd denominator `302231454903657293676545` is now closed
for power-of-two numerators:
`problem2_10_denominator_two_pow_seventy_eight_plus_one_eq_power_sum`
and
`problem2_10_two_pow_seventy_eight_plus_one_allowableDenominator`
prove `302231454903657293676545 = 2^78 + 2^0`;
`problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_eight_plus_one`
and
`problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_eight_plus_one`
prove the source integer-side hypotheses for `m = +/-2^k` under
`k < ieeeDoubleFormat.t - 1`;
`problem2_10_ieeeDouble_two_pow_two_pow_seventy_eight_plus_one_denominator_rounds_to_upper`
proves the first rounded division sends `(2^k)/302231454903657293676545` to
`9007199254740992 * 2^(k-131)`;
`problem2_10_ieeeDouble_div_two_pow_two_pow_seventy_eight_plus_one_exact_mul_two_pow_seventy_eight_plus_one_above`
proves the exact product with `302231454903657293676545` is `2^k + 2^(k-78)`;
the existing
`problem2_10_ieeeDouble_two_pow_plus_one_sixtysevenmilliononehundredeightthousandeighthundredsixtyfourth_ulp_rounds_to_two_pow`
proves the final round returns `2^k`; and
`problem2_10_ieeeDouble_signed_two_pow_two_pow_seventy_eight_plus_one_denominator_times_two_pow_seventy_eight_plus_one`
packages the signed finite-selector trace
`fl(((+/-2^k)/302231454903657293676545)*302231454903657293676545) = +/-2^k` for `k <= 1022`.
The displayed-prefix denominator `12` is now closed for shifted power-of-two
numerators as well: `problem2_10_denominator_twelve_eq_power_sum` and
`problem2_10_twelve_allowableDenominator` prove `12 = 2^3 + 2^2`;
`problem2_10_two_pow_add_two_numerator_kahan_hypotheses_of_twelve` and
`problem2_10_negative_two_pow_add_two_numerator_kahan_hypotheses_of_twelve`
prove the source integer-side hypotheses for `m = +/-2^(k+2)` under
`k + 3 < ieeeDoubleFormat.t`;
`problem2_10_ieeeDouble_div_two_pow_add_two_twelve` proves the first rounded
division reuses the denominator-`3` quotient for `(2^k)/3`;
`problem2_10_ieeeDouble_div_two_pow_add_two_twelve_exact_mul_twelve_midpoint`
proves the exact product with `12` is the midpoint
`2^(k+2) - 2^((k+2)-54)`; and
`problem2_10_ieeeDouble_signed_two_pow_add_two_twelfths_times_twelve` packages
the signed finite-selector trace
`fl(((+/-2^(k+2))/12)*12) = +/-2^(k+2)` for `k <= 1021`.
The displayed-prefix denominator `18` is now closed for shifted power-of-two
numerators on the denominator-`9` route:
`problem2_10_denominator_eighteen_eq_power_sum` and
`problem2_10_eighteen_allowableDenominator` prove `18 = 2^4 + 2^1`;
`problem2_10_two_pow_succ_numerator_kahan_hypotheses_of_eighteen` and
`problem2_10_negative_two_pow_succ_numerator_kahan_hypotheses_of_eighteen`
prove the source integer-side hypotheses for `m = +/-2^(k+1)` under
`k + 2 < ieeeDoubleFormat.t`;
`problem2_10_ieeeDouble_div_two_pow_succ_eighteen` proves the first rounded
division reuses the denominator-`9` quotient for `(2^k)/9`;
`problem2_10_ieeeDouble_div_two_pow_succ_eighteen_exact_mul_eighteen_midpoint`
proves the exact product with `18` is the midpoint
`2^(k+1) - 2^((k+1)-54)`; and
`problem2_10_ieeeDouble_signed_two_pow_succ_eighteenths_times_eighteen`
packages the signed finite-selector trace
`fl(((+/-2^(k+1))/18)*18) = +/-2^(k+1)` for `k <= 1022`.
The displayed-prefix denominator `20` is now closed for shifted power-of-two
numerators on the denominator-`5` route:
`problem2_10_denominator_twenty_eq_power_sum` and
`problem2_10_twenty_allowableDenominator` prove `20 = 2^4 + 2^2`;
`problem2_10_two_pow_add_two_numerator_kahan_hypotheses_of_twenty` and
`problem2_10_negative_two_pow_add_two_numerator_kahan_hypotheses_of_twenty`
prove the source integer-side hypotheses for `m = +/-2^(k+2)` under
`k + 3 < ieeeDoubleFormat.t`;
`problem2_10_ieeeDouble_div_two_pow_add_two_twenty` proves the first rounded
division reuses the denominator-`5` quotient for `(2^k)/5`;
`problem2_10_ieeeDouble_div_two_pow_add_two_twenty_exact_mul_twenty_above`
proves the exact product with `20` is
`2^(k+2) + 2^((k+2)-54)`; and
`problem2_10_ieeeDouble_signed_two_pow_add_two_twentieths_times_twenty`
packages the signed finite-selector trace
`fl(((+/-2^(k+2))/20)*20) = +/-2^(k+2)` for `k <= 1020`.

For `m = 1`, `problem2_10_ieeeDouble_div_one_three_exact_mul_three_midpoint`
records the actual second-operation exact product after rounded division,
`fl(1/3) * 3 = 1 - 2^-54`, and
`problem2_10_ieeeDouble_midpoint_below_one_rounds_to_one` rounds that midpoint
tie to `1`; the signed companion theorems prove the `m = -1` trace via
`-1 + 2^-54` and final tie to `-1`.  The `m = 2` branch proves `2/3` first
rounds to `6004799503160661 * 2^-53`, the exact product is `2 - 2^-53`, and
`problem2_10_ieeeDouble_midpoint_below_two_rounds_to_two` rounds that midpoint
tie to `2`; the signed `m = -2` branch follows by round-to-even oddness, with
exact product `-2 + 2^-53` and final tie to `-2`.  The `m = 4` branch proves
`4/3` first rounds to `6004799503160661 * 2^-52`, the exact product is
`4 - 2^-52`, and `problem2_10_ieeeDouble_midpoint_below_four_rounds_to_four`
rounds that midpoint tie to `4`; the signed `m = -4` branch follows by
round-to-even oddness, with exact product `-4 + 2^-52` and final tie to `-4`.
The `m = 8` branch proves `8/3` first rounds to
`6004799503160661 * 2^-51`, the exact product is `8 - 2^-51`, and
`problem2_10_ieeeDouble_midpoint_below_eight_rounds_to_eight` rounds that
midpoint tie to `8`; the signed `m = -8` branch follows by round-to-even
oddness, with exact product `-8 + 2^-51` and final tie to `-8`.  The `m = 16`
branch proves `16/3` first rounds to `6004799503160661 * 2^-50`, the exact
product is `16 - 2^-50`, and
`problem2_10_ieeeDouble_midpoint_below_sixteen_rounds_to_sixteen` rounds that
midpoint tie to `16`; the signed `m = -16` branch follows by round-to-even
oddness, with exact product `-16 + 2^-50` and final tie to `-16`.  The
`m = 32` branch proves `32/3` first rounds to
`6004799503160661 * 2^-49`, the exact product is `32 - 2^-49`, and
`problem2_10_ieeeDouble_midpoint_below_thirtytwo_rounds_to_thirtytwo` rounds
that midpoint tie to `32`; the signed `m = -32` branch follows by
round-to-even oddness, with exact product `-32 + 2^-49` and final tie to `-32`.

The packaged theorems `problem2_10_ieeeDouble_signed_two_thirds_times_three`,
`problem2_10_ieeeDouble_signed_four_thirds_times_three`,
`problem2_10_ieeeDouble_signed_eight_thirds_times_three`,
`problem2_10_ieeeDouble_signed_sixteen_thirds_times_three`, and
`problem2_10_ieeeDouble_signed_thirtytwo_thirds_times_three` record the signed
numerator-`2`, numerator-`4`, numerator-`8`, numerator-`16`, and
numerator-`32` results.  Remaining Problem 2.10 work is the nonzero-numerator
quantified rounded-arithmetic theorem for non-representable quotients beyond
the closed denominator-`3`, denominator-`5` power-of-two, denominator-`5`
`3*2^k` numerator, denominator-`9`, denominator-`17`, denominator-`33`,
denominator-`65`, denominator-`129`, denominator-`257`, denominator-`513`,
denominator-`1025`, denominator-`2049`, denominator-`4097`,
denominator-`8193`, denominator-`16385`, denominator-`32769`,
denominator-`65537`, denominator-`131073`, denominator-`262145`,
denominator-`524289`, denominator-`1048577`, denominator-`2097153`,
denominator-`4194305`, denominator-`8388609`, denominator-`16777217`,
denominator-`33554433`, denominator-`67108865`, denominator-`134217729`,
denominator-`268435457`, denominator-`536870913`, denominator-`1073741825`,
denominator-`2147483649`, denominator-`4294967297`, denominator-`8589934593`,
denominator-`17179869185`, denominator-`34359738369`, denominator-`68719476737`,
denominator-`137438953473`, denominator-`274877906945`, denominator-`549755813889`,
denominator-`1099511627777`,
denominator-`2199023255553`,
denominator-`4398046511105`,
denominator-`8796093022209`,
denominator-`17592186044417`,
denominator-`35184372088833`,
denominator-`70368744177665`,
denominator-`140737488355329`,
denominator-`281474976710657`,
denominator-`562949953421313`,
denominator-`1125899906842625`,
denominator-`2251799813685249`,
denominator-`4503599627370497`,
denominator-`9007199254740993`,
denominator-`18014398509481985`,
denominator-`36028797018963969`,
denominator-`72057594037927937`,
denominator-`144115188075855873`,
denominator-`288230376151711745`,
denominator-`576460752303423489`,
denominator-`1152921504606846977`,
denominator-`2305843009213693953`,
denominator-`4611686018427387905`,
denominator-`9223372036854775809`,
denominator-`18446744073709551617`,
denominator-`36893488147419103233`,
denominator-`73786976294838206465`,
denominator-`147573952589676412929`,
denominator-`295147905179352825857`,
denominator-`590295810358705651713`,
denominator-`1180591620717411303425`,
denominator-`2361183241434822606849`,
denominator-`4722366482869645213697`,
denominator-`9444732965739290427393`,
denominator-`18889465931478580854785`,
denominator-`37778931862957161709569`,
denominator-`75557863725914323419137`,
denominator-`151115727451828646838273`,
denominator-`302231454903657293676545`,
shifted-power denominator-`6`, and denominator-`6` numerator-`1`,
shifted-power denominator-`10`, and denominator-`10` numerator-`1`, shifted-power denominator-`12`,
shifted-power denominator-`18`, and shifted-power denominator-`20` families,
plus the full IEEE
instruction/special-value/flag semantics layer.  The
dedicated bottleneck ledger for this surviving theorem family is
`docs/CHAPTER02_PROBLEM2_10_BOTTLENECK.md`.

C2.21 Problem 2.27 update note: `Problem2_27.lean` now closes the source residual convergence-test argument at the additive-underflow model layer.  `FloatingPointFormat.problem2_27_convergenceTest_fullAccuracy_of_additive_model_normal_branch` proves that zero computed residual plus the normal (2.8) branch certifies full accuracy, and `FloatingPointFormat.problem2_27_convergenceTest_fullAccuracy_or_underflow_bound_of_additive_model` records the gradual-underflow eta-bound alternative when that branch is not known.

## Not-Proved Ledger

The full Chapter 2 gate remains open on the following paper-level items:

| Priority | Item | Blocking foundation |
|---|---|---|
| P0 | C2.5 finite floating-point rounding policy and C2.6 Theorem 2.2 operational surface | The finite-format vocabulary, finite range predicates/classifiers, signed subnormal grid, overflow saturation, finite-normal Theorem 2.2/2.3 relation theorems, arbitrary finite choices `finiteNearestFl`/`finiteNormalFl`, finite-normal round-away `finiteNormalRoundAway`, finite-normal round-to-even `finiteNormalRoundToEven`, finite-normal directed selectors `finiteNormalRoundTowardNegative`/`finiteNormalRoundTowardPositive`/`finiteNormalRoundTowardZero`, finite underflow directed selectors, total finite directed selectors `finiteRoundTowardNegative`/`finiteRoundTowardPositive`/`finiteRoundTowardZero`, finite mode selector `finiteRoundToMode`, total source-facing finite round-away `finiteRoundAway`, total source-facing finite round-to-even `finiteRoundToEven`, local adjacent-bracket round-to-even selector `nearestAdjacentRoundToEven`, local adjacent directed endpoint selectors, ordinary finite operation wrappers `finiteRoundToEvenOp`/`finiteRoundToEvenSqrt`, exact representable-result wrappers, finite flag-free IEEE-facing wrappers, the first flagged IEEE overflow/underflow/invalid-operation default results, division-by-zero infinite-result predicates, signed-zero denominator value-selection lemmas, and ordinary finite-zero denominator default lemmas, the primitive-operation plus square-root invalid/overflow/underflow dispatches, mode-parameterized primitive-operation and square-root overflow/underflow/no-flags dispatches through `finiteRoundToModeOp`/`finiteRoundToModeSqrt`, directed primitive-operation and square-root overflow aliases, primitive quiet-NaN/invalid-operation special predicates, modeled NaN unordered/unequal, signed-zero equality, and predicate-level comparison-completeness predicates, and the first square-root signed-zero/NaN/positive-infinity/negative-infinity branches are proved.  Still open: remaining infinities and special-value propagation beyond the first primitive/square-root/comparison predicate branches, signaling-NaN/payload behavior, full concrete comparison instruction semantics beyond the predicate layer, traps, full directed operation semantics beyond primitive/square-root finite branches, and deriving a total `FPModel`/IEEE primitive operation from concrete semantics. |
| P0 | C2.12--C2.13 Ferguson/Sterbenz exact subtraction | The theorem-surface predicates and bridge are named by `fergusonExponentCondition`, `guardDigitSubtractionModel`, `sterbenzRatioCondition`, and `sterbenzFergusonBridgeCondition`; exactness follows for routines satisfying the guard model.  The first Ferguson proof reductions are now proved by `fergusonExponentCondition_exponent_gap_le_one`, `fergusonExponentCondition_same_sign_and_exponent_gap`, and `fergusonExponentCondition_same_sign_exponent_cases`, the normalized `x-y` side condition gives no-underflow/no-overflow facts, the raw same-exponent/one-exponent-shift aligned subtraction identities are proved, the same-exponent mantissa difference is bounded by the `t`-digit mantissa limit and preserved by modeled `t`-digit coefficient rounding, the normalized-difference same-exponent branch is proved finite by `normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_normalizedDiff`, the one-base-shift same-exponent branch is proved finite by `normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_beta_mul_normalizedDiff`, the arbitrary finite radix-power shift branch is proved finite by `normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_beta_pow_mul_normalizedDiff`, the `emin` below-threshold same-exponent branch is proved finite by `normalizedValue_sub_sameSign_sameExponent_finiteSystem_at_emin_of_natAbs_lt_minNormalMantissa`, the shifted `emin` subnormal endpoint and same-exponent normalized-mantissa source theorem are proved by `normalizedValue_sub_sameSign_sameExponent_finiteSystem_at_shifted_emin_of_natAbs_mul_beta_pow_lt_minNormalMantissa` and `normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_normalizedMantissas`, the one-shift guard coefficient is bounded below the normalized leading-digit threshold in both adjacent orientations, the `z1 = 0` leading-digit sentence is formalized for the `t+1` guard word, the adjacent-exponent guard-word rounding step is proved exact in both orientations, `guardDigitBranchSubtractionModel` packages the same-exponent/high-minus-low/low-minus-high case split and proves it satisfies `guardDigitSubtractionModel`, `guardDigitRoundedBranchSubtractionValue_finiteSystem_of_ferguson` and `GuardDigitBranchSubtractionData.branchValue_finiteSystem` integrate the derived same-exponent selector into branch finite-system output, `guardDigitBranchSubtractionRoutine_exact_of_fergusonCondition` and `guardDigitBranchSubtractionRoutine_finiteSystem_of_fergusonCondition` instantiate exactness and finite output for a noncomputable evidence-selecting branch routine, and `finiteRoundToEvenOp_sub_sameSign_sameExponent_eq_exact`, `finiteRoundToEvenOp_sub_positive_adjacentExponent_eq_exact_of_sterbenzAdjacent`, `finiteRoundToEvenOp_sub_positive_eq_exact_of_sterbenzRatioCondition`, `finiteRoundToEvenOp_sub_normalizedSystem_eq_exact_of_sterbenzRatioCondition`, `finiteRoundToEvenOp_sub_sameSign_subnormal_eq_exact`, `finiteRoundToEvenOp_sub_subnormalSystem_eq_exact_of_sterbenzRatioCondition`, `finiteRoundToEvenOp_sub_normalizedSystem_subnormalSystem_eq_exact_of_sterbenzRatioCondition`, `finiteRoundToEvenOp_sub_subnormalSystem_normalizedSystem_eq_exact_of_sterbenzRatioCondition`, `finiteRoundToEvenOp_sub_finiteSystem_eq_exact_of_sterbenzRatioCondition`, `finiteRoundToEvenOp_sub_eq_exact_of_guardDigitBranchSubtractionData`, and `finiteRoundToEvenOp_sub_eq_exact_of_fergusonCondition` connect the same-exponent, positive normalized Sterbenz, all-subnormal Sterbenz, mixed normal/subnormal Sterbenz, source-facing finite-system all-case Sterbenz, and Ferguson-data surfaces to concrete finite round-to-even subtraction.  The Sterbenz ratio-distance lemmas, the direct positive adjacent coefficient bound `guardAlignedMantissaDiffInt_natAbs_lt_mantissaBound_of_sterbenzAdjacent`, the finite-system theorem `normalizedValue_sub_positive_adjacentExponent_finiteSystem_of_sterbenzAdjacent`, the ratio-symmetry and exponent-gap theorems `sterbenzRatioCondition_symm` and `sterbenzRatioCondition_positive_normalized_exponent_gap_le_one`, the positive normalized finite-system theorem `normalizedValue_sub_positive_finiteSystem_of_sterbenzRatioCondition`, the normalized-system wrapper `normalizedSystem_sub_finiteSystem_of_sterbenzRatioCondition`, the all-subnormal finite-system theorem `subnormalSystem_sub_finiteSystem_of_sterbenzRatioCondition`, the mixed finite-system theorems `normalizedValue_sub_subnormalValue_positive_finiteSystem_of_sterbenzRatioCondition`, `normalizedSystem_sub_subnormalSystem_finiteSystem_of_sterbenzRatioCondition`, and `subnormalSystem_sub_normalizedSystem_finiteSystem_of_sterbenzRatioCondition`, the source-facing all-case theorem `finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition`, and the exact finite round-to-even theorems `finiteRoundToEvenOp_sub_positive_eq_exact_of_sterbenzRatioCondition`, `finiteRoundToEvenOp_sub_normalizedSystem_eq_exact_of_sterbenzRatioCondition`, and `finiteRoundToEvenOp_sub_subnormalSystem_eq_exact_of_sterbenzRatioCondition` are proved, and `decimalSingleDigitFormat_sterbenzRatio_not_ferguson` rules out the previous plan to derive Ferguson's exponent condition from Sterbenz's ratio condition in general bases.  Still missing: a fully executable digit-level/full IEEE subtraction implementation and the corresponding full IEEE operation theorem. |
| P0 | C2.20 underflow model (2.8) | Additive witness algebra, gradual/flush eta-bound constants, the finite-normal no-underflow branch, the non-strict source-facing gradual-underflow branch, strict no-half-tie variants, finite directed underflow selectors, finite flag-free result embeddings, the first flagged IEEE overflow/underflow/invalid-operation default results, division-by-zero infinite-result predicates, signed-zero denominator value-selection lemmas, and ordinary finite-zero denominator default lemmas, primitive-operation plus square-root invalid/overflow/underflow result dispatches, mode-parameterized primitive-operation and square-root overflow/underflow result dispatch through `ieeeUnderflowModeResult`, finite-normal directed endpoint selectors, primitive quiet-NaN/invalid-operation special predicates, modeled NaN unordered/unequal, signed-zero equality, and predicate-level comparison-completeness predicates, and the first square-root signed-zero/NaN/positive-infinity/negative-infinity branches are proved.  Still missing: traps, signaling-NaN/payload behavior, remaining special-value behavior beyond signed-zero denominator division-by-zero predicate cases, full concrete comparison instruction semantics beyond the predicate layer, full IEEE operation semantics, and directed-mode additive-underflow bounds if needed beyond the current one-sided mode evidence. |
| P1 | C2.8 concrete IEEE formats and ulp/wobbling facts | Concrete single/double parameter instances, unit-roundoff values, single/double ulp exponent formulas, generic `ulpAtExponent`, adjacent-gap ulp witnesses, relative wobbling-precision bounds including the IEEE-single Figure 2.1 numerical interval, MATLAB/Fortran machine-epsilon convention adapters, IEEE-facing value/result/flag/mode vocabulary, flagged overflow/underflow/default-result constructors including division-by-zero infinite-result predicates, signed-zero denominator value-selection lemmas, and ordinary finite-zero denominator default lemmas, primitive quiet-NaN/invalid-operation special predicates, modeled NaN unordered/unequal, signed-zero equality, and predicate-level comparison-completeness predicates, mode-parameterized primitive-operation and square-root overflow and finite-branch dispatch, and finite directed endpoint/total selector layers are closed; traps, signaling-NaN/payload behavior, full concrete comparison instruction semantics beyond the predicate layer, remaining special values beyond signed-zero denominator division-by-zero predicate cases, and full IEEE semantics remain open. |
| P1 | C2.19 finite FMA versus full IEEE FMA | The finite real-valued single-rounding FMA wrapper is closed by `FloatingPointFormat.finiteRoundToEvenFMA_eq_round_exact`, `FloatingPointFormat.finiteRoundToEvenFMA_eq_exact_of_finiteSystem`, and `FloatingPointFormat.finiteRoundToEvenFMA_standardModel_lt_of_finiteNormalRange`.  This is not full IEEE FMA: flags, special values, signed zeros, infinities, NaNs, traps, payloads, directed-mode special branches, and hardware-specific semantics remain open. |
| P1 | C2.19 finite chopping bias versus historical execution trace | The finite theorem-bearing chopping claim is closed by `FloatingPointFormat.finiteRoundTowardZero_error_nonpos_of_nonneg`, `FloatingPointFormat.finiteRoundTowardZero_error_nonneg_of_nonpos`, the operation-mode wrappers `FloatingPointFormat.finiteRoundToModeOp_towardZero_error_nonpos_of_exact_nonneg` and `FloatingPointFormat.finiteRoundToModeOp_towardZero_error_nonneg_of_exact_nonpos`, and the accumulated one-sided sum theorem `FloatingPointFormat.finiteRoundTowardZero_sum_errors_nonpos_of_nonneg`.  The concrete Vancouver three-decimal final-value floor-scaling routine is closed by `decimalChopThree`, `decimalChopThree_abs_error_lt_one_thousandth`, `decimalChopThree_grid_eq`, `decimalChopThree_initial_index`, and `decimalChopThree_sum_errors_nonpos`.  Still open: reconstructing the historical Vancouver Stock Exchange update data and a full executable IEEE/decimal trace. |
| P1 | C2.19 tie rules: decimal example versus stability/drift theorem | The exact decimal tie example is closed by `FloatingPointFormat.decimal_2445_roundToEven_chain` and `FloatingPointFormat.decimal_2445_roundToOdd_chain`, with `FloatingPointFormat.nearestAdjacentRoundToOdd` providing the local round-to-odd tie selector dual to the existing round-to-even selector.  Concrete local one-decimal Reiser--Knuth-shaped add/sub traces are closed by `FloatingPointFormat.decimalOnePlaceRoundToEven_reiserKnuth_stable_from_one` and `FloatingPointFormat.decimalOnePlaceRoundToOdd_reiserKnuth_stable_after_first_step`, and the contrasting local round-away drift trace is closed by `FloatingPointFormat.decimalOnePlaceRoundAway_drift_first_two_steps`.  Still open: the full general Reiser--Knuth repeated add/sub stability theorem for round-to-even/round-to-odd over arbitrary inputs/brackets/formats. |
| P1 | C2.19 monotonic correctly rounded arithmetic beyond local brackets | The local adjacent-bracket round-to-even monotonicity foundation is closed by `FloatingPointFormat.nearestAdjacentRoundToEven_monotone_on_ordered_bracket`, plus endpoint bounds for the same selector.  Still open: lifting this same-bracket theorem through the total finite selector across underflow/normal/overflow branches and then through concrete primitive-operation monotonicity assumptions; full IEEE monotonicity also needs special-value, signed-zero, NaN, infinity, flag, trap, and directed-mode semantics. |
| P2 | C2.15--C2.16 distribution/statistical claims | C2.15's displayed logarithmic leading-digit probability law is now closed by `logarithmicLeadingDigitProbability`, with strict mass decrease and decimal nonuniformity proved by `logarithmicLeadingDigitMass_succ_lt` and `decimalLogarithmicLeadingDigitProbability_nonuniform`; the algebraic base-power scale-invariance surface is closed by `logarithmicIntervalMass_mul_base_zpow` and `logarithmicLeadingDigitMass_scaled_bin_zpow`.  Remaining C2.15 work is Brent's base-optimality theorem, the stronger scale-invariance-equivalence theorem, product-convergence/equidistribution claims, and empirical examples.  C2.16's finite second-moment square-root rule is now closed by `StatisticalRoundingErrorModel.rms_sum_le_sqrt_card_mul_unit`; remaining C2.16 work is deriving those assumptions from concrete random rounding, proving CLT/asymptotic normality, and formalizing PRECISE/CESTAC/logarithmic-mantissa models if desired. |
| P2 | C2.17 alternative number systems | The precise level-index encoding/decoding formula is now formalized by `levelIndexForward`, `levelIndexBackward_forward`, and `LevelIndexCode`.  Remaining claims are intentionally descriptive unless the project grows a full alternative-arithmetic semantics: range/cost comparisons, controversy/comparative evaluation, and the other cited systems. |
| P2 | C2.18 accuracy tests and C2.21 problems | C2.18 now has exact real-arithmetic baselines in `AccuracyTests.lean`, including a certified reduced-argument identity and sign/coarse magnitude bound for `sin(22)`, a five-term odd Taylor remainder theorem below `10^-20` for that sine target, a certified half-last-place interval for the Table 2.4 exact-row displayed `sin(22)` decimal, certified half-last-place intervals for both exact-source displayed decimals of `2.5^125`, and a small-error theorem for the exponentiation sensitivity sentence; remaining C2.18 work requires concrete IEEE/executable arithmetic semantics for the historical table outputs.  C2.21 has problem-numbered finite-format or model-level theorem surfaces for Problems 2.1--2.7, the base-10 part and finite-sequence audit of Problem 2.8, the finite-selector Problem 2.9 calculation, the displayed finite-selector Problem 2.10 Kahan instance, the Problem 2.11 empirical leading-digit histogram surface, the Problem 2.12 reciprocal-product classifier, the Problem 2.13 finite-wrapper candidate/predecessor crossing and all-earlier minimality proof with finite IEEE-double input certificates, the Problem 2.14 double and single Kahan probe traces, the Problems 2.15--2.16 special-value probes, Problems 2.17--2.23, the exact-intermediate and zero-result branch audits plus modeled finite single/double nonzero closure for Problem 2.24, the Problem 2.25 exact-residual FMA determinant core, the Problem 2.26 reciprocal Newton algebra plus rounded-step local-error/exact-intermediate finite branch, and the Problem 2.27 residual convergence-test model; detailed theorem names and remaining per-problem caveats are listed in the updates below.  It still requires Problem 2.8's concrete full guard-digit/IEEE operation-semantics lift beyond the exact-step theorem surface, the remaining nonzero-numerator quantified Problem 2.10 Kahan theorem for non-representable quotients, language/library-specific empirical runs for Problem 2.16 if desired, actual external datasets/histograms for Problem 2.11 if desired, and full IEEE operation semantics with flags/traps/special values where noted. |

Problem 2.11 empirical leading-digit update: `problem2_11EmpiricalSource` enumerates the five source families named in the exercise, and `problem2_11_powerSample` plus `problem2_11_factorialSample` name the generated samples `2^n`, `3^n` for `n = 0:1000` and `n!` for `n = 1:1000`.  `problem2_11_powerSample_card`, `problem2_11_powerSample_index_le_1000`, `problem2_11_powerSample_first`, `problem2_11_powerSample_last`, `problem2_11_powerSample_two_last`, and `problem2_11_powerSample_three_last` make the source power-sample cardinality, index range, and endpoints explicit; `problem2_11_factorialSample_card`, `problem2_11_factorialSample_index_between`, `problem2_11_factorialSample_first`, and `problem2_11_factorialSample_last` do the same for the factorial sample.  The existing positivity proofs close the nonzero side condition for the generated power and factorial data.  `problem2_11_decimalLeadingDigit` records the decade-cell leading-digit predicate; `problem2_11_decimalLeadingDigit_normalized_bin` proves that division by the witnessed power of `10` places `|x|` in the corresponding digit bin, and `problem2_11_decimalLeadingDigit_exists_scaled_mem_one_ten` proves the source note's coarser `[1,10)` normalization range.  `problem2_11_digitCount` and `problem2_11_digitFrequency` define the finite empirical histogram for any classifier; `problem2_11_digitCount_le_sampleSize`, `problem2_11_digitFrequency_nonneg`, and `problem2_11_digitFrequency_le_one` prove the per-digit probability bounds; and `problem2_11_sum_digitCount_eq_sampleSize`, `problem2_11_sum_digitFrequency_eq_one`, `problem2_11_empiricalDigitProbability`, and `problem2_11_empiricalDigitProbability_prob_le_one` prove that the normalized frequencies form a finite probability distribution on digits `1, ..., 9` with each probability at most `1`.  Remaining Problem 2.11 scope is actual data import/computation for random symmetric matrix eigenvalues, physical constants, newspaper numbers, and any displayed numerical histogram outputs.

Problem 2.12 reciprocal-product update: `problem2_12_ieeeDouble_reciprocal_product_rounding_options` closes the source-shaped finite real-valued IEEE-double operation-wrapper theorem.  For every real `x` with `1 < x < 2`, `problem2_12_ieeeDouble_reciprocal_finiteNormalRange_of_one_lt_x_lt_two` proves `1/x` is finite-normal, `problem2_12_ieeeDouble_reciprocal_product_mem_window_of_one_lt_x_lt_two` proves the actual rounded-reciprocal product `x * fl(1/x)` lies in `[1 - 2^-53, 1 + 2^-53]`, and `problem2_12_ieeeDouble_final_rounding_options_of_mem_window` gives the final classifier: finite IEEE-double round-to-even returns either `1 - 2^-53 = 1 - eps/2` or `1`.  Remaining gaps are full IEEE instruction/special-value/flag semantics and Problem 2.13's smallest failing `j`.

Problem 2.13 candidate-failure update: `problem2_13_sourceX`, `problem2_13_sourceProduct`, `problem2_13_sourceX_candidateJ`, and `problem2_13_sourceX_predecessorJ` name the source family `x_j = 1 + j*2^-52`, the exact product `x_j*fl(1/x_j)` after the rounded reciprocal, and the candidate and predecessor inputs.  `problem2_13_predecessorJ_succ_eq_candidateJ`, `problem2_13_candidateX_sub_predecessorX_eq_ulp`, and `problem2_13_predecessorX_add_ulp_eq_candidateX` prove the one-ulp/source-index adjacency, while `problem2_13_sourceX_le_sourceX`, `problem2_13_sourceX_le_predecessorX_of_lt_candidateJ`, and `problem2_13_sourceX_lt_candidateX_of_lt_candidateJ` prove that every source index below `257736490` gives an input no larger than the certified predecessor and strictly below the failing candidate.  `problem2_13_sourceX_finiteSystem_of_lt_two_pow_52` and `problem2_13_sourceX_finiteSystem_of_lt_candidateJ` prove that every source input in the relevant index range is itself a finite IEEE-double value.  `problem2_13_sourceX_between_one_two_of_pos_lt_candidateJ`, `problem2_13_sourceX_rounding_options_of_pos_lt_candidateJ`, and `problem2_13_sourceProduct_mem_window_of_pos_lt_candidateJ` specialize the Problem 2.12 classifier and product-window theorem to every positive source index below the candidate.  The branch selectors `problem2_13_sourceX_rounds_to_predecessor_of_sourceProduct_lt_lower_midpoint`, `problem2_13_sourceX_rounds_to_one_of_lower_midpoint_le`, and `problem2_13_sourceX_rounds_to_one_iff_lower_midpoint_le` prove that, for earlier source inputs, selecting the final `1` branch is equivalent to proving `1 - 2^-54 <= x_j*fl(1/x_j)`.  `problem2_13_candidateX_finiteSystem`, `problem2_13_predecessorX_finiteSystem`, `problem2_13_predecessor_candidate_adjacentNormalized`, `problem2_13_predecessorX_lt_candidateX`, `problem2_13_candidate_rounds_to_predecessor`, and `problem2_13_candidate_rounds_ne_one` prove that `j = 257736490` is a genuine finite-input failing case for the finite real-valued IEEE-double operation wrapper.  The candidate source-product theorems `problem2_13_sourceProduct_candidateJ`, `problem2_13_sourceProduct_candidateJ_mem_window`, `problem2_13_candidate_sourceProduct_lt_lower_midpoint`, and `problem2_13_candidate_rounds_to_predecessor_of_sourceProduct_lower_midpoint` prove that the candidate input is finite IEEE-double, lies in `(1,2)`, has rounded reciprocal `9007198739268041 * 2^-53`, has source product `1 - 2251799886937606*2^-105` below the lower midpoint, and rounds through the source-product lower branch to `1 - 2^-53`, not `1`.  The adjacent source-product theorems `problem2_13_sourceProduct_predecessorJ`, `problem2_13_predecessor_sourceProduct_lower_midpoint_le`, and `problem2_13_predecessor_rounds_to_one_of_sourceProduct_lower_midpoint`, together with `problem2_13_predecessor_rounds_to_one`, prove that `j = 257736489` is also a finite IEEE-double input, has source product `1 - 2251798855991677*2^-105`, satisfies the lower-midpoint inequality, and still rounds to `1`.  The later all-earlier wrapper `problem2_13_sourceX_rounds_to_one_of_pos_lt_candidateJ` closes the finite real-valued IEEE-double operation-wrapper minimality statement for every positive `j < 257736490`; the remaining Problem 2.13 scope is the full IEEE instruction/special-value/flag semantics layer.

Problem 2.13 scaled-product update: `problem2_13_sourceProduct_eq_scaled_of_reciprocal_rounds` rewrites `x_j*fl(1/x_j)` as `((2^52 + j)*k)*2^-105` whenever the rounded reciprocal is `k*2^-53`.  `problem2_13_sourceProduct_lower_midpoint_le_of_scaled_product_ge` and `problem2_13_sourceProduct_lt_lower_midpoint_of_scaled_product_lt` prove that the integer threshold `2^105 - 2^51` exactly controls the lower-midpoint comparison, and `problem2_13_sourceX_rounds_to_one_iff_reciprocal_scaled_product_ge` proves that, for every positive earlier source index, the final rounded product is `1` iff `2^105 - 2^51 <= (2^52 + j)*k`.  `problem2_13_sourceX_rounds_to_one_of_left_reciprocal_nat_certificate`, `problem2_13_sourceX_rounds_to_one_of_right_reciprocal_nat_certificate`, `problem2_13_sourceX_rounds_to_predecessor_of_left_reciprocal_nat_certificate`, and `problem2_13_sourceX_rounds_to_predecessor_of_right_reciprocal_nat_certificate` compose the Nat reciprocal-cell/midpoint certificates with that final scaled-product threshold for both possible adjacent reciprocal endpoints.  `problem2_13_sourceX_rounds_to_one_of_left_reciprocal_quotient_certificate` and `problem2_13_sourceX_rounds_to_one_of_right_reciprocal_quotient_certificate` further specialize the success branch to the quotient `floor(2^105/(2^52+j))`, replacing the interval hypotheses by the nonzero-remainder fact.  `problem2_13_reciprocalCellQuotient_remainder_ne_zero_of_pos_lt_candidateJ` proves that nonzero-remainder fact for every `0 < j < 257736490`, and `problem2_13_reciprocalCellQuotient_remainder_not_half_of_pos_lt_candidateJ` rules out exact half-remainder ties in the same range.  `problem2_13_sourceX_rounds_to_one_of_left_reciprocal_quotient_integer_certificate` and `problem2_13_sourceX_rounds_to_one_of_right_reciprocal_quotient_integer_certificate` additionally discharge the quotient mantissa-range hypotheses from `0 < j < 257736490`, while `problem2_13_sourceX_rounds_to_one_of_left_reciprocal_quotient_remainder_certificate` and `problem2_13_sourceX_rounds_to_one_of_right_reciprocal_quotient_remainder_certificate` replace the midpoint-side hypotheses by direct comparisons between `2*((2^105) % (2^52+j))` and `2^52+j`.  `problem2_13_reciprocalCellQuotient_scaled_product_left_ge_of_remainder_le` reduces the left-endpoint final scaled-product certificate to `((2^105) % (2^52+j)) <= 2^51`, and `problem2_13_reciprocalCellQuotient_scaled_product_right_ge` proves the right-endpoint final scaled-product certificate unconditionally.  The final wrappers `problem2_13_sourceX_rounds_to_one_of_left_reciprocal_quotient_remainder_le_threshold`, `problem2_13_sourceX_rounds_to_one_of_left_reciprocal_quotient_remainder_lt_half_le_threshold`, and `problem2_13_sourceX_rounds_to_one_of_right_reciprocal_quotient_remainder_gt_half` expose those reduced obligations, with the new left-wrapper discharging the nonzero-remainder side condition from `0 < j < 257736490`.  `problem2_13_quadraticRemainderQuotient` names `floor(2*j^2/(2^52+j))`; `problem2_13_quadraticRemainderQuotient_le_29_of_lt_candidateJ` proves this small quotient is at most `29` below the candidate, `problem2_13_reciprocalCellQuotient_remainder_eq_quadratic_remainder_of_lt_candidateJ` rewrites the original `2^105` remainder as `(2*j^2) % (2^52+j)`, and `problem2_13_reciprocalCellQuotient_remainder_le_threshold_of_quadraticQuotient_eq_29` closes the left-branch threshold throughout the top band.  The wrappers `problem2_13_sourceX_rounds_to_one_of_left_reciprocal_quadraticQuotient_eq_29` and `problem2_13_sourceX_rounds_to_one_of_quadraticQuotient_eq_29` prove that every positive earlier source index in the top band rounds back to `1`.  The lower-band theorem `problem2_13_reciprocalCellQuotient_remainder_le_threshold_of_quadraticQuotient_le_28_of_left`, together with `problem2_13_sourceX_rounds_to_one_of_left_reciprocal_quadraticQuotient_le_28` and `problem2_13_sourceX_rounds_to_one_of_quadraticQuotient_le_28`, closes the remaining quotient bands `<= 28`.  The final wrapper `problem2_13_sourceX_rounds_to_one_of_pos_lt_candidateJ` proves that every positive source index below the candidate rounds back to `1`.  `problem2_13_candidate_scaled_product_lt_lower_midpoint_threshold` and `problem2_13_predecessor_scaled_product_ge_lower_midpoint_threshold` expose the integer crossing at the candidate/predecessor boundary, while `problem2_13_predecessor_rounds_to_one_of_scaled_product_certificate` shows the predecessor branch through the certificate theorem.  The remaining Problem 2.13 scope is full IEEE instruction/special-value/flag semantics.

Problem 2.13 reciprocal-certificate update: `problem2_13_sourceX_eq_scaled` proves the source grid identity `x_j = (2^52 + j)*2^-52`.  `problem2_13_sourceX_reciprocal_strict_between_of_scaled_interval` turns the scaled integer-cell inequalities `k*(2^52+j) < 2^105 < (k+1)*(2^52+j)` into the strict real reciprocal interval `k*2^-53 < 1/x_j < (k+1)*2^-53`, and `problem2_13_sourceX_reciprocal_strict_between_of_nat_scaled_interval` exposes the same bridge directly from Nat inequalities.  `problem2_13_reciprocalCellQuotient` names `floor(2^105/(2^52+j))`; `problem2_13_reciprocalCellQuotient_nat_scaled_interval` and `problem2_13_sourceX_reciprocal_strict_between_of_quotient_remainder` prove that a nonzero remainder gives the strict adjacent reciprocal cell for that quotient, while `problem2_13_reciprocalCellQuotient_remainder_ne_zero_of_pos_lt_candidateJ` proves the required nonzero remainder for every positive source index below the candidate.  `problem2_13_reciprocalCellQuotient_remainder_not_half_of_pos_lt_candidateJ` and `problem2_13_reciprocalCellQuotient_remainder_half_trichotomy_of_pos_lt_candidateJ` additionally rule out exact reciprocal-cell midpoint ties and split the remainder comparison into left or right branches.  `problem2_13_reciprocalCellQuotient_normalizedMantissas_of_pos_lt_candidateJ` proves that, for every positive source index below the candidate, the quotient and its successor are normalized IEEE-double mantissas.  `problem2_13_reciprocalCellQuotient_midpoint_left_of_twice_remainder_lt` and `problem2_13_reciprocalCellQuotient_midpoint_right_of_denominator_lt_twice_remainder` convert the quotient midpoint-side tests to direct remainder-half comparisons.  `problem2_13_sourceX_reciprocal_left_closer_of_scaled_midpoint` and `problem2_13_sourceX_reciprocal_right_closer_of_scaled_midpoint` turn the integer midpoint tests `2^106 < (2*k+1)*(2^52+j)` and `(2*k+1)*(2^52+j) < 2^106` into the corresponding endpoint-closeness inequalities.  `problem2_13_sourceX_reciprocal_rounds_to_left_of_scaled_interval_midpoint`, `problem2_13_sourceX_reciprocal_rounds_to_right_of_scaled_interval_midpoint`, `problem2_13_sourceX_reciprocal_rounds_to_left_of_nat_interval_midpoint`, `problem2_13_sourceX_reciprocal_rounds_to_right_of_nat_interval_midpoint`, `problem2_13_sourceX_reciprocal_rounds_to_left_of_quotient_midpoint`, `problem2_13_sourceX_reciprocal_rounds_to_right_of_quotient_midpoint`, `problem2_13_sourceX_reciprocal_rounds_to_left_of_quotient_midpoint_of_pos_lt_candidateJ`, `problem2_13_sourceX_reciprocal_rounds_to_right_of_quotient_midpoint_of_pos_lt_candidateJ`, `problem2_13_sourceX_reciprocal_rounds_to_left_of_quotient_remainder_lt_half`, and `problem2_13_sourceX_reciprocal_rounds_to_right_of_quotient_remainder_gt_half` compose those interval, quotient, mantissa-range, midpoint, and remainder-half certificates with the adjacent IEEE-double round-to-even wrappers.  This closes the reusable real/Nat/quotient adjacent-cell, nonzero-remainder, no-tie, normalized-mantissa, and midpoint-to-remainder adapters consumed by the all-earlier-`j` audit; the lower-band quotient-remainder classification and left-branch remainder threshold are now supplied by the scaled-product theorem above.

Problem 2.14 Kahan probe update: `problem2_14_ieeeDouble_four_thirds_rounds_to_lower`, `problem2_14_ieeeDouble_four_thirds_minus_one`, `problem2_14_ieeeDouble_three_mul_four_thirds_minus_one`, and `problem2_14_ieeeDouble_kahan_probe_error` close the finite IEEE-double round-to-even operation-wrapper trace for `|3*(4/3 - 1) - 1|`.  The first double division rounds `4/3` to `6004799503160661*2^-52`, the exact rounded subtraction gives `6004799503160660*2^-54`, multiplication by `3` gives `1 - 2^-52`, and the final subtraction gives signed error `-2^-52`; `problem2_14_ieeeDoubleKahanEstimate_eq_two_unitRoundoff` proves the absolute probe is `2*u`.  The single-precision companion trace is closed by `problem2_14_ieeeSingle_four_thirds_rounds_to_upper`, `problem2_14_ieeeSingle_four_thirds_minus_one`, `problem2_14_ieeeSingle_three_mul_four_thirds_minus_one`, and `problem2_14_ieeeSingle_kahan_probe_error`: single rounds `4/3` to `11184811*2^-23`, the exact rounded subtraction gives `11184812*2^-25`, multiplication by `3` gives `1 + 2^-23`, and the final subtraction gives signed error `2^-23`; `problem2_14_ieeeSingleKahanEstimate_eq_two_unitRoundoff` proves the absolute probe is again `2*u`.  Remaining Problem 2.14 scope is only additional empirical "machines available" runs and full IEEE instruction/special-value/flag semantics.

Problems 2.15--2.16 elementary special-value probe update: `problem2_15_16Probe` records the exact source probes `0^0`, `1^inf`, `2^inf`, `exp(inf)`, `exp(-inf)`, `sign(NaN)`, `sign(-NaN)`, `NaN^0`, `inf^0`, `1^NaN`, `log(inf)`, `log(-inf)`, and `log(0)`.  `problem2_15_16ProbeList`, `problem2_15_16ProbeList_length`, `problem2_15_16ProbeList_nodup`, and `problem2_15_16Probe_mem_sourceList` package the source list, prove that it has length `13`, prove that it has no duplicates, and prove that every formal probe constructor is present.  `problem2_15_16ReferenceResult` gives a concrete quiet/default reference convention, with `problem2_15_reference_zero_pow_zero` proving that the reference answer to Problem 2.15 is `1` with no flags, while `problem2_15_16ReferenceEnvironment_eval` identifies the reference environment with the reference result table.  The `problem2_16_reference_*` theorems expose the corresponding reference outputs for the listed Problem 2.16 probes.  `problem2_15_16_probe_not_forced_by_core_ieee_model` proves the important source warning formally: the repository's core IEEE primitive-operation model does not force a unique result for any such elementary-function probe without adding an implementation-specific elementary library.  Remaining Problem 2.16 scope is only empirical language/library runs or a chosen implementation-specific elementary-function semantics.

Problem 2.17 rounded discriminant update: `problem2_17_standard_model_counterexample` proves that the source's sign-loss phenomenon can occur in the standard model for the rounded path `fl(fl(b*b) - fl(a*c))` before computing `sqrt(b^2-a*c)` in `a*x^2 - 2*b*x + c = 0`.  The concrete witness has `a = 1`, `b = 1`, and `c = 9/10`, so `problem2_17_true_discriminant_eq_one_tenth` proves the true discriminant-like quantity is exactly `b^2 - a*c = 1/10`; `problem2_17_standard_model_witness_exact_values` exhibits a valid abstract `FPModel` with `u = 1/10` whose rounded path computes exactly `-9/100`.  The strengthened theorem `problem2_17_standard_model_counterexample_with_decimal_finite_inputs` proves that those same inputs are finite values of the one-digit decimal format, using `FloatingPointFormat.problem2_17_decimalOneDigitThreeExponentFormat_finiteSystem_nine_tenths` for `9/10`.  Remaining Problem 2.17 scope is a concrete finite-operation or hardware/IEEE trace tying the rounded operations themselves to an actual format, range, rounding-mode, and exception model.

Problem 2.18 exponent-gap strengthening update: `problem2_18_exponent_gap_not_sufficient_for_exact_subtraction` refutes the proposed replacement of Ferguson's cancellation side condition by positivity plus normalized exponents differing by at most one.  The finite-selector witness uses the one-digit decimal format with `x = 20` and `y = 1`: `problem2_18_twenty_one_exponent_gap` proves the operands are positive normalized values with exponents `2` and `1`, `problem2_18_nineteen_finiteNormalRange` proves the exact difference `19` is in the normal range, `problem2_18_nineteen_not_finiteSystem` proves it is not representable, and `problem2_18_sub_twenty_one_rounds_to_twenty` proves finite round-to-even subtraction returns `20`, not `19`.  The packaged theorem `problem2_18_source_counterexample_exact_values` records the same source-facing witness in one statement: exponent-gap hypothesis, exact difference `19`, normal-range but nonrepresentable difference, rounded value `20`, and failure of exact subtraction.  Remaining Problem 2.18 scope is only a concrete hardware/IEEE operation semantics instantiation; the mathematical strengthening is false at the finite-selector layer.

Problem 2.19 square-root identity update: `FloatingPointFormat.problem2_19_sqrt_square_eq_abs_of_finiteSystem` proves the reasonable source requirement at the finite round-to-even square-root layer: for any finite floating-point input `x`, the exact square-root input `x^2` returns `|x|`.  `FloatingPointFormat.problem2_19_roundedSqrtSquare_not_abs_counterexample` refutes the stronger rounded-root-then-square requirement: in the one-digit decimal format, `FloatingPointFormat.problem2_19_decimalOneDigitThreeExponent_sqrt_two_rounds_to_one` proves `fl(sqrt(2)) = 1`, and `FloatingPointFormat.problem2_19_decimalOneDigitThreeExponent_roundedSqrtSquare_two_eq_one` proves the squared rounded-root path returns `1`, not `|2|`.  The answer theorem `FloatingPointFormat.problem2_19_first_requirement_holds_second_fails` packages both sides of the source question: the first requirement holds for every finite input in any finite selector format, while the second fails with finite input `2` in the one-digit decimal format.  Remaining Problem 2.19 scope is only full IEEE square-root/multiplication semantics with special values, flags, and traps.

Problem 2.20 naive norm-ratio update: `problem2_20_exactRatio_abs_le_one` and `problem2_20_exactRatio_le_one` prove the source Euclidean baseline that the exact ratio `x / sqrt(x^2+y^2)` has absolute value at most `1`, hence is at most `1`, for all real components.  `problem2_20_standard_model_counterexample` proves that the source's rounded `x / sqrt(x^2+y^2)` phenomenon can occur in the abstract Higham standard model.  The witness has `x = 11/10` and `y = 0`: `problem2_20_exact_witness_ratio_eq_one` proves the exact real ratio is `1`, while a valid `FPModel` with `u = 1/5` rounds the first square `(11/10)^2` down to `1`; the square-root and final division are exact, and `problem2_20_computed_witness_ratio_gt_one` proves the computed ratio is `11/10 > 1`.  The strengthened theorem `problem2_20_standard_model_counterexample_with_decimal_finite_inputs` also proves that the standard-model witness inputs are finite values of the local two-digit decimal format `FloatingPointFormat.problem2_20_decimalTwoDigitThreeExponentFormat`, with `FloatingPointFormat.problem2_20_decimalTwoDigitThreeExponentFormat_finiteSystem_eleven_tenths` certifying `11/10`.  The finite-selector companion `FloatingPointFormat.problem2_20_decimalOneDigitThreeExponent_finite_selector_counterexample` closes a concrete one-digit decimal round-to-even operation trace over real inputs: `problem2_20_exact_three_halves_zero_ratio_eq_one` proves the exact ratio for `x = 3/2`, `y = 0` is `1`, while `FloatingPointFormat.problem2_20_decimalOneDigitThreeExponent_computed_ratio_eq_two` proves the rounded path returns `2`; the trace explicitly rounds `(3/2)^2` to `2`, keeps `0^2` and `2+0` exact, reuses the Problem 2.19 proof that `sqrt(2)` rounds to `1`, and rounds `(3/2)/1` to the even endpoint `2`.  The audit theorem `problem2_20_decimalOneDigitThreeExponent_three_halves_not_finiteSystem` proves that this one-digit trace is not a finite-input trace, since `3/2` is not a finite value of the chosen format.  The range audit `FloatingPointFormat.problem2_20_decimalOneDigitThreeExponent_exact_trace_range_audit` proves that the nonzero exact intermediates in this trace are finite-normal but the exact zero square is in the finite underflow range.  The predicate `FloatingPointFormat.problem2_20_noSquareUnderflowInputs` names the two-square no-underflow audit condition, and `FloatingPointFormat.problem2_20_components_ne_zero_of_noSquareUnderflowInputs` proves that this condition forces both components to be nonzero.  The packaged theorem `FloatingPointFormat.problem2_20_decimalOneDigitThreeExponent_trace_exceeds_one_but_fails_source_audit` records that the current one-digit trace exceeds `1` but fails the source audit because `3/2` is not finite in the chosen format and `0*0` underflows.  Remaining Problem 2.20 scope is a concrete finite-selector or IEEE instruction trace with finite inputs, nonzero components, and the source's no-overflow/no-underflow side condition, plus full IEEE instruction semantics with flags, traps, and special values.

Problem 2.21 naive maximum update: `ieeeNaiveMax` formalizes the literal `if x > y then x else y` code path over the modeled IEEE value/comparison layer.  `ieeeNaiveMax_finite_finite_left_of_lt`, `ieeeNaiveMax_finite_finite_right_of_le`, and `ieeeNaiveMax_finite_finite_eq_max` prove that, on ordinary finite real operands, the branch returns the usual real maximum.  `ieeeNaiveMax_left_nan`, `ieeeNaiveMax_right_nan`, `ieeeNaiveMax_nan_finite`, `ieeeNaiveMax_finite_nan`, `ieeeNaiveMax_nan_finite_ne_finite_nan`, `ieeeNaiveMax_left_nan_finite_result_not_nan`, `ieeeNaiveMax_concrete_nan_counterexample`, and `ieeeNaiveMax_not_nan_propagating` prove the source-shaped counterexample: because modeled IEEE `>` is false when either operand is NaN, a left NaN with finite right operand is discarded, while a right NaN is returned.  Thus the branch is not symmetric in NaN cases and does not implement a NaN-propagating maximum.  The packaged theorem `ieeeNaiveMax_finite_correct_but_not_nan_propagating` states both sides of the source answer: finite operands are handled correctly, but the code does not always produce the NaN-propagating answer.  Remaining Problem 2.21 scope is full IEEE max/min instruction semantics, signaling-NaN/payload behavior, and trap/flag details.

Problem 2.22 Kahan Heron guard-digit update: `problem2_22_guard_digit_a_sub_b_exact` packages the Theorem 2.5/Sterbenz guard-digit step needed by the source hint, proving that the parenthesized `a-b` subtraction in Kahan's Heron formula is exact under the ordered-side finite-system hypotheses.  `problem2_22_kahanHeronArea_relError_le_gamma9_unitRoundoff` exposes the problem-numbered theorem surface for the already-formalized finite trace: under the explicit finite-normal side conditions on the remaining rounded intermediates, nonnegative radicand, square-root/final-area range hypotheses, and `gammaValid` side condition, the computed Kahan area has relative error bounded by `(1 + gamma_9) * (1 + u)^2 - 1` relative to the exact Kahan expression.  Remaining Problem 2.22 scope is a full IEEE/special-value/flag instantiation and any theorem that removes the listed finite-normal range hypotheses from source-level geometric assumptions.

Problem 2.23 guard-digit/no-guard update: `problem2_23_guardDigitY_eq_x_of_finiteSystem` proves the finite exact/guard-digit result for the source sequence `y = (x+x)-x`: when `x` and `x+x` remain in the finite system, the rounded sequence returns `x`.  `problem2_23_noGuardY_error_formula` exposes the corresponding abstract no-guard model formula, with all four input perturbations from the rounded add and rounded subtract visible in `y-x = x*(alpha+beta+2*gamma+alpha*gamma+beta*gamma-eta)`.  The binary mantissa theorems `problem2_23_binaryNoGuardScaledMantissa_eq_add_mod_two`, `problem2_23_binaryNoGuardScaledMantissa_eq_self_of_even`, `problem2_23_binaryNoGuardScaledMantissa_eq_succ_of_odd`, `problem2_23_binaryNoGuardYScaled_error_eq_low_bit`, and `problem2_23_binaryNoGuardYScaled_eq_scaledValue_add_low_bit` capture the source digit-level description: after alignment without a guard digit, the dropped low bit changes the scaled mantissa from `m` to `m + m%2`, equivalently adding `(m%2)*scale` to the original scaled value.  The packaged theorem `problem2_23_guard_and_binary_noGuard_summary` states the guard-digit and binary no-guard conclusions together.  Remaining Problem 2.23 scope is full executable binary hardware semantics, overflow/underflow behavior, and IEEE special-value/flag details.

Problem 2.24 Kahan nonzero-expression update: `FloatingPointFormat.problem2_24_eval` defines the literal finite round-to-even path for `(((x - 0.5) + x) - 0.5) + x`, and `FloatingPointFormat.problem2_24_y1`, `FloatingPointFormat.problem2_24_y2`, and `FloatingPointFormat.problem2_24_y3` expose the three rounded intermediates.  `FloatingPointFormat.problem2_24_exactExpr_eq_three_mul_sub_one`, `FloatingPointFormat.problem2_24_exactExpr_eq_zero_iff`, and `FloatingPointFormat.problem2_24_exactExpr_ne_zero_of_ne_one_third` prove that the exact source expression is `3*x - 1`, vanishes exactly at `x = 1/3`, and is nonzero for inputs different from `1/3`; `FloatingPointFormat.problem2_24_ieeeSingle_half_finiteSystem` and `FloatingPointFormat.problem2_24_ieeeDouble_half_finiteSystem` prove that the literal constant `0.5` is finite in the modeled IEEE single and double formats.  `FloatingPointFormat.problem2_24_eval_eq_rounded_last_sum`, `FloatingPointFormat.problem2_24_eval_eq_last_exact_of_finiteSystem_last_sum`, `FloatingPointFormat.problem2_24_eval_eq_zero_iff_last_sum_eq_zero_of_finiteSystem_last_sum`, `FloatingPointFormat.problem2_24_y3_eq_neg_x_of_eval_eq_zero_of_finiteSystem_last_sum`, and `FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_last_sum_of_last_sum_ne_zero` close the final-exact branch: if `y3 + x` is finite representable, the final rounded addition is exact, so rounded zero is equivalent to exact zero of the last sum, a zero result forces `y3 = -x`, and a nonzero exact last sum rules out a zero result.  `FloatingPointFormat.problem2_24_eval_eq_exactExpr_of_finiteSystem_intermediates` proves the rounded path equals the literal source expression when all four exact real intermediates are finite representable; `FloatingPointFormat.problem2_24_eval_eq_three_mul_sub_one_of_finiteSystem_intermediates` simplifies that expression to `3*x - 1`, and `FloatingPointFormat.problem2_24_eq_one_third_of_eval_eq_zero_of_finiteSystem_intermediates` proves a zero result in this branch forces `x = 1/3`.  The reusable theorem `FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_intermediates_of_ne_one_third` packages the corresponding nonzero conclusion for any input known not to be `1/3`; the contrapositive theorems `FloatingPointFormat.problem2_24_eval_eq_zero_implies_not_all_finiteSystem_intermediates_of_ne_one_third` and `FloatingPointFormat.problem2_24_eval_eq_zero_implies_exists_nonfinite_exact_intermediate_of_ne_one_third` turn any zero result away from `1/3` into an explicit nonfinite exact-intermediate branch.  `FloatingPointFormat.finiteRoundToEven_eq_zero_abs_le_half_minSubnormalMagnitude_of_subnormalMantissa_one` proves the finite-selector converse that a zero round-to-even result forces the exact input within half a smallest-subnormal spacing when that smallest subnormal exists, and `FloatingPointFormat.problem2_24_eval_eq_zero_last_sum_abs_le_half_minSubnormalMagnitude` applies it to the final exact sum `y3+x`.  The finite-grid separation lemmas `FloatingPointFormat.finiteSystem_exists_int_mul_minSubnormalMagnitude`, `FloatingPointFormat.int_mul_minSubnormalMagnitude_abs_ge_of_ne_zero`, and `FloatingPointFormat.finiteSystem_add_eq_zero_of_abs_le_half_minSubnormalMagnitude`, together with `FloatingPointFormat.problem2_24_y3_finiteSystem`, prove that a finite-system input with a zero result must have exact final cancellation: `FloatingPointFormat.problem2_24_eval_eq_zero_last_sum_eq_zero_of_finiteSystem_input` gives `y3+x=0`, and `FloatingPointFormat.problem2_24_y3_eq_neg_x_of_eval_eq_zero_of_finiteSystem_input` gives `y3=-x`.  The rounded-intermediate finiteness lemmas `FloatingPointFormat.problem2_24_y1_finiteSystem` and `FloatingPointFormat.problem2_24_y2_finiteSystem`, the first-step nearestness lemmas `FloatingPointFormat.problem2_24_y1_first_sub_nearestRoundingToFinite`, `FloatingPointFormat.problem2_24_y1_first_sub_distance_to_x_le_half`, and `FloatingPointFormat.problem2_24_y1_between_x_sub_one_and_x_of_finiteSystem_input`, the second-step nearestness lemmas `FloatingPointFormat.problem2_24_y2_second_add_nearestRoundingToFinite`, `FloatingPointFormat.problem2_24_y2_second_add_distance_to_zero_le_self`, `FloatingPointFormat.problem2_24_y2_second_add_distance_to_y1_le_abs_x`, and `FloatingPointFormat.problem2_24_y2_second_add_distance_to_x_le_abs_y1`, the third-step nearestness lemmas `FloatingPointFormat.problem2_24_y3_eq_neg_x_last_sub_nearestRoundingToFinite`, `FloatingPointFormat.problem2_24_y3_eq_neg_x_last_sub_minimal`, and `FloatingPointFormat.problem2_24_y3_eq_neg_x_last_sub_distance_to_y2_le_half`, and the finite-input wrappers `FloatingPointFormat.problem2_24_eval_eq_zero_last_sub_minimal_of_finiteSystem_input`, `FloatingPointFormat.problem2_24_eval_eq_zero_last_sub_distance_to_y2_le_half_of_finiteSystem_input`, `FloatingPointFormat.problem2_24_eval_eq_zero_y2_add_x_between_zero_and_one_of_finiteSystem_input`, `FloatingPointFormat.problem2_24_eval_eq_zero_input_nonneg_of_finiteSystem_input`, `FloatingPointFormat.problem2_24_eval_eq_zero_input_le_one_of_finiteSystem_input`, and `FloatingPointFormat.problem2_24_eval_eq_zero_input_mem_unit_interval_of_finiteSystem_input` further prove that this exact cancellation makes `-x` a nearest finite value of `y2-0.5`, so comparing against the finite candidate `y2` forces `|y2+x-0.5| <= 0.5`; combining that third-step interval with first- and second-step nearestness forces `0 <= y2+x <= 1` and `0 <= x <= 1` for any finite zero counterexample.  `FloatingPointFormat.problem2_24_y2_second_add_distance_to_x_product_le_of_finiteSystem_input` and `FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_input_of_half_le` additionally rule out every finite-system zero counterexample with `x >= 0.5`.  `FloatingPointFormat.problem2_24_ieeeSingle_oneThird_rounds_to_upper` proves the IEEE-single finite selector rounds `1/3` to `11184811 * 2^-25`; together with the existing IEEE-double `1/3` rounding theorem, `FloatingPointFormat.problem2_24_ieeeSingle_one_third_not_finiteSystem` and `FloatingPointFormat.problem2_24_ieeeDouble_one_third_not_finiteSystem` prove that `1/3` is not a finite input in either format.  The named wrappers `FloatingPointFormat.problem2_24_ieeeSingle_finiteSystem_ne_one_third` and `FloatingPointFormat.problem2_24_ieeeDouble_finiteSystem_ne_one_third` expose this as a reusable fact for arbitrary finite IEEE single/double inputs, and `FloatingPointFormat.problem2_24_ieeeSingle_exactExpr_ne_zero_of_finiteSystem` and `FloatingPointFormat.problem2_24_ieeeDouble_exactExpr_ne_zero_of_finiteSystem` show that the exact source expression is already nonzero on such inputs.  The branch theorems `FloatingPointFormat.problem2_24_ieeeSingle_eval_ne_zero_of_finiteSystem_intermediates` and `FloatingPointFormat.problem2_24_ieeeDouble_eval_ne_zero_of_finiteSystem_intermediates` close the exact-intermediate single/double case, while `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_implies_exists_nonfinite_exact_intermediate` and `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_implies_exists_nonfinite_exact_intermediate` prove that any finite IEEE single/double zero counterexample must enter one of the four nonfinite exact-intermediate branches.  The IEEE wrappers `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_last_sum_eq_zero_of_finiteSystem_input`, `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_last_sum_eq_zero_of_finiteSystem_input`, `FloatingPointFormat.problem2_24_ieeeSingle_y3_eq_neg_x_of_eval_eq_zero_of_finiteSystem_input`, `FloatingPointFormat.problem2_24_ieeeDouble_y3_eq_neg_x_of_eval_eq_zero_of_finiteSystem_input`, `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_implies_y3_eq_neg_x_and_exists_nonfinite_exact_intermediate`, `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_implies_y3_eq_neg_x_and_exists_nonfinite_exact_intermediate`, `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_last_sub_distance_to_y2_le_half_of_finiteSystem_input`, `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_last_sub_distance_to_y2_le_half_of_finiteSystem_input`, `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_input_mem_unit_interval_of_finiteSystem_input`, `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_input_mem_unit_interval_of_finiteSystem_input`, `FloatingPointFormat.problem2_24_ieeeSingle_eval_ne_zero_of_finiteSystem_input_of_half_le`, and `FloatingPointFormat.problem2_24_ieeeDouble_eval_ne_zero_of_finiteSystem_input_of_half_le` package the counterexample audit: exact final cancellation, a nonfinite source exact intermediate, the third-step distance inequality, the unit-interval input condition, and the exclusion of `x >= 0.5`.  The lower-half tightening theorems narrow any modeled finite zero counterexample to `3/10 <= x <= 5/12` generically, and the `-3/8` comparison sharpens the IEEE upper endpoint to `x <= 3/8`.  The finite-grid representation theorem `FloatingPointFormat.problem2_24_ieeeSingle_third_exact_intermediate_finiteSystem_of_finiteSystem_zero_branch` and its double analogue prove that the third exact real intermediate is finite throughout this localized IEEE zero branch, contradicting the global third-nonfinite witness.  Consequently `FloatingPointFormat.problem2_24_ieeeSingle_eval_ne_zero_of_finiteSystem_input` and `FloatingPointFormat.problem2_24_ieeeDouble_eval_ne_zero_of_finiteSystem_input` close the modeled finite single/double round-to-even path.  Remaining Problem 2.24 scope is full IEEE operation semantics with flags, traps, infinities, and NaNs.

Problem 2.24 first exact-intermediate closure update: `FloatingPointFormat.problem2_24_first_exact_intermediate_finiteSystem_of_quarter_lt_of_lt_one` packages the Sterbenz-exact first subtraction as a finite-system fact for the exact intermediate `x-0.5`.  `FloatingPointFormat.problem2_24_eval_eq_zero_first_exact_intermediate_finiteSystem_of_finiteSystem_input` applies the current zero-branch interval to prove that every modeled finite zero counterexample has this first exact intermediate finite.  Therefore `FloatingPointFormat.problem2_24_eval_eq_zero_implies_later_nonfinite_exact_intermediate_of_finiteSystem_input_of_ne_one_third`, with IEEE wrappers `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_implies_later_nonfinite_exact_intermediate` and `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_implies_later_nonfinite_exact_intermediate`, shrinks the nonfinite-exact-intermediate branch from four possibilities to the later three exact intermediates.  The sharper theorem `FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_input_of_ne_one_third_of_second_third_exact_intermediates` proves that a finite zero branch away from `1/3` is impossible if both the second and third exact real intermediates are finite: the first subtraction is already exact, the next two operations become exact, and exact final cancellation gives `x = 1/3`.  Hence `FloatingPointFormat.problem2_24_eval_eq_zero_implies_second_or_third_nonfinite_exact_intermediate_of_finiteSystem_input_of_ne_one_third`, with IEEE wrappers `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_implies_second_or_third_nonfinite_exact_intermediate` and `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_implies_second_or_third_nonfinite_exact_intermediate`, shrinks every finite single/double zero branch to a failure of one of the next two exact intermediates.  The later sub-third, upper-branch, and localized third-representability refinements close this branch for modeled finite IEEE single/double inputs; full IEEE special-value/flag semantics remain separate.

Problem 2.24 sub-third second exact-intermediate closure update: `FloatingPointFormat.problem2_24_second_exact_intermediate_finiteSystem_of_quarter_lt_of_lt_one_third` packages the exact second addition in the lower sub-third Sterbenz branch as a finite-system fact for `(x-0.5)+x`.  `FloatingPointFormat.problem2_24_eval_eq_zero_second_exact_intermediate_finiteSystem_of_finiteSystem_input_of_lt_one_third` applies this to any modeled finite zero branch with `x < 1/3`.  Therefore `FloatingPointFormat.problem2_24_eval_eq_zero_implies_last_two_nonfinite_exact_intermediate_of_finiteSystem_input_of_lt_one_third`, with IEEE wrappers `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_implies_last_two_nonfinite_exact_intermediate_of_lt_one_third` and `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_implies_last_two_nonfinite_exact_intermediate_of_lt_one_third`, shrinks the sub-third nonfinite-exact-intermediate branch from the later three possibilities to the third or final exact real intermediate.  The stronger theorem `FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_input_of_lt_one_third_of_third_exact_intermediate_finiteSystem` proves that a zero result is impossible below `1/3` if the third exact real intermediate is finite: the third subtraction becomes exact, so exact final cancellation gives `x = 1/3`.  Hence `FloatingPointFormat.problem2_24_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_finiteSystem_input_of_lt_one_third`, with IEEE wrappers `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_lt_one_third` and `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_lt_one_third`, leaves only the third exact real intermediate as the possible nonfinite witness in the sub-third zero branch.  The branch at or above `1/3` is closed by adjacent no-gap and upper-neighbor classification lemmas, yielding `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_implies_third_exact_intermediate_nonfinite` and `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_implies_third_exact_intermediate_nonfinite`; the subsequent localized third-representability theorem contradicts that witness and closes the modeled finite path.

Problem 2.24 finite-IEEE closure update: `FloatingPointFormat.problem2_24_ieeeSingle_third_exact_intermediate_finiteSystem_of_neg_one_mantissa_mem_zero_branch` and `FloatingPointFormat.problem2_24_ieeeDouble_third_exact_intermediate_finiteSystem_of_neg_one_mantissa_mem_zero_branch` prove that positive exponent-`-1` mantissas in the localized zero-branch interval have finite third exact real intermediate `2*x-1`.  `FloatingPointFormat.problem2_24_ieeeSingle_finiteSystem_zero_branch_exists_neg_one_mantissa` and `FloatingPointFormat.problem2_24_ieeeDouble_finiteSystem_zero_branch_exists_neg_one_mantissa` classify every finite IEEE single/double value in `[3/10,3/8]` as such a mantissa.  The wrappers `FloatingPointFormat.problem2_24_ieeeSingle_third_exact_intermediate_finiteSystem_of_finiteSystem_zero_branch` and `FloatingPointFormat.problem2_24_ieeeDouble_third_exact_intermediate_finiteSystem_of_finiteSystem_zero_branch` contradict the previously proved global third-nonfinite zero witness, yielding `FloatingPointFormat.problem2_24_ieeeSingle_eval_ne_zero_of_finiteSystem_input` and `FloatingPointFormat.problem2_24_ieeeDouble_eval_ne_zero_of_finiteSystem_input`: no modeled finite IEEE single/double input makes the finite round-to-even Problem 2.24 expression evaluate to zero.  Remaining Problem 2.24 scope is only the lift to full IEEE operation semantics with flags, traps, infinities, and NaNs.

Problem 2.24 product-constraint follow-up: `FloatingPointFormat.problem2_24_y3_eq_neg_x_last_sub_distance_to_zero_product_le` compares the exact-cancellation candidate `-x` with the finite candidate zero at the third subtraction and proves `x*(2*y2+x-1) <= 0`; `FloatingPointFormat.problem2_24_y3_eq_neg_x_last_sub_y2_bound_of_pos` specializes this to `2*y2+x <= 1` for positive inputs.  The finite-input wrappers `FloatingPointFormat.problem2_24_eval_eq_zero_last_sub_distance_to_zero_product_le_of_finiteSystem_input` and `FloatingPointFormat.problem2_24_eval_eq_zero_last_sub_y2_bound_of_pos_finiteSystem_input`, plus the IEEE single/double wrappers, record this product/positive-input `y2` constraint in the zero-branch audit used by the later closure theorem.

Problem 2.24 first-step sign-cell follow-up: `FloatingPointFormat.problem2_24_y1_first_sub_distance_to_zero_product_le` compares the first rounded intermediate with the finite candidate zero and proves the algebraic constraint `y1*(y1-(2*x-1)) <= 0`.  The midpoint split theorems `FloatingPointFormat.problem2_24_y1_between_zero_and_two_mul_x_sub_one_of_half_le` and `FloatingPointFormat.problem2_24_y1_between_two_mul_x_sub_one_and_zero_of_le_half`, with their one-sided component lemmas, package this as `0 <= y1 <= 2*x-1` for `x >= 1/2` and `2*x-1 <= y1 <= 0` for `x <= 1/2`.  This records a first-step sign split aligned with the source expression's midpoint for the zero-branch audit.

Problem 2.24 second-step sign-cell follow-up: `FloatingPointFormat.problem2_24_y2_second_add_distance_to_zero_product_le` compares the second rounded intermediate with the finite candidate zero and proves `y2*(y2-2*(y1+x)) <= 0`.  The split theorems `FloatingPointFormat.problem2_24_y2_between_zero_and_two_mul_y1_add_x_of_y1_add_x_nonneg` and `FloatingPointFormat.problem2_24_y2_between_two_mul_y1_add_x_and_zero_of_y1_add_x_nonpos`, with their one-sided component lemmas, package this as `0 <= y2 <= 2*(y1+x)` when `y1+x >= 0` and `2*(y1+x) <= y2 <= 0` when `y1+x <= 0`.  This adds the second-step analogue of the first-step sign-cell split for the remaining exact-cancellation branch.

Problem 2.24 lower-half tightening follow-up: `FloatingPointFormat.problem2_24_y2_second_add_distance_to_x_le_abs_y1` compares the second rounded intermediate with the finite input candidate `x`, and `FloatingPointFormat.problem2_24_y2_second_add_distance_to_x_product_le_of_finiteSystem_input` proves `(x-y2)*(2*y1+x-y2) <= 0` for finite inputs.  Combining this product constraint with the first-step midpoint split and the third-step positive-input bound proves `FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_input_of_half_le`: no finite-system zero counterexample can have `x >= 0.5`.  `FloatingPointFormat.problem2_24_eval_zero_ne_zero_of_half_and_one_finiteSystem` excludes the endpoint `x = 0` whenever `0.5` and `1` are finite.  The third-step comparison against finite candidate `-0.5`, formalized by `FloatingPointFormat.problem2_24_y3_eq_neg_x_last_sub_distance_to_neg_half_product_nonneg`, gives `1/2 <= 2*y2+x` in the lower half; the finite-input wrappers `FloatingPointFormat.problem2_24_eval_eq_zero_y2_pos_of_lt_half_finiteSystem_input` and `FloatingPointFormat.problem2_24_eval_eq_zero_y1_add_x_pos_of_lt_half_finiteSystem_input` then force `y2 > 0` and `y1+x > 0`.  The theorem `FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_input_of_lt_one_six` rules out `x < 1/6` by combining `y2 > x` with the candidate-`x` product and `y1 <= 0`, and `FloatingPointFormat.problem2_24_eval_eq_zero_input_mem_one_six_to_half_of_finiteSystem_input` packages that intermediate branch as `1/6 <= x < 1/2`.  The first-step comparison against finite candidate `-x`, formalized by `FloatingPointFormat.problem2_24_y1_first_sub_distance_to_neg_x_product_nonneg_of_finiteSystem_input`, gives `y1 <= 3*x-1` whenever the lower-half zero branch has `y1+x > 0`; combining this with the second-step sign cell and the `-0.5` third-step lower bound proves `FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_input_of_lt_nine_thirty_four` and packages the intermediate modeled finite-input branch as `9/34 <= x < 1/2` in `FloatingPointFormat.problem2_24_eval_eq_zero_input_mem_nine_thirty_four_to_half_of_finiteSystem_input`, with IEEE single/double wrappers.  Sterbenz exactness for the first subtraction, formalized by `FloatingPointFormat.problem2_24_y1_eq_x_sub_half_of_finiteSystem_input_of_quarter_lt_of_lt_one`, then combines with the second-step sign cell and the `-0.5` third-step lower bound to prove `FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_input_of_lt_five_eighteen` and packages the intermediate modeled finite-input branch as `5/18 <= x < 1/2` in `FloatingPointFormat.problem2_24_eval_eq_zero_input_mem_five_eighteen_to_half_of_finiteSystem_input`, with IEEE single/double wrappers.  The third-step comparison against finite candidate `y1`, formalized by `FloatingPointFormat.problem2_24_y3_eq_neg_x_last_sub_distance_to_y1_product_nonneg`, gives `2*y2-y1+x <= 1` on the positive lower branch; with `y1 = x-1/2` this proves `FloatingPointFormat.problem2_24_eval_eq_zero_y2_le_quarter_of_finiteSystem_input`, and the candidate-`x` second-step product proves `FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_input_of_five_twelfths_lt`, packaging the upper side as `x <= 5/12`.  In the sub-third branch, `FloatingPointFormat.problem2_24_y2_eq_two_mul_x_sub_half_of_finiteSystem_input_of_quarter_lt_of_lt_one_third` proves the second addition Sterbenz-exact; combined with the third-step lower bound, this proves `FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_input_of_lt_three_tenths` and packages the remaining modeled finite-input branch as `3/10 <= x <= 5/12` in `FloatingPointFormat.problem2_24_eval_eq_zero_input_mem_three_tenths_to_five_twelfths_of_finiteSystem_input`, with IEEE single/double wrappers.  The arbitrary finite negative-constant comparison `FloatingPointFormat.problem2_24_y3_eq_neg_x_last_sub_distance_to_neg_const_product_le` specializes to `-3/8` to prove `FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_input_of_three_eighths_lt`, and to `-11/32` plus the sub-third exact-second-addition branch to prove the older `FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_input_of_lt_fifty_three_one_sixty` lower exclusion.  The parametric lower theorem `FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_input_of_const_gt_one_third_of_lt_two_sub_const_div_five` shows that any finite candidate `-a` with `a > 1/3` rules out `x < (2-a)/5`.  The IEEE finite-value certificates now include `FloatingPointFormat.problem2_24_ieeeSingle_one_third_upper_neighbor_finiteSystem` and `FloatingPointFormat.problem2_24_ieeeDouble_one_third_upper_neighbor_finiteSystem`, so the wrappers `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_input_mem_one_third_upper_neighbor_lower_to_three_eighths_of_finiteSystem_input` and `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_input_mem_one_third_upper_neighbor_lower_to_three_eighths_of_finiteSystem_input` package the current finite IEEE branches as `(2 - 11184811 * 2^-25)/5 <= x <= 3/8` for single and `(2 - 6004799503160662 * 2^-54)/5 <= x <= 3/8` for double.  The finite-grid adapters `FloatingPointFormat.problem2_24_ieeeSingle_second_exact_intermediate_finiteSystem_of_neg_one_mantissa_mem_upper_branch` and `FloatingPointFormat.problem2_24_ieeeDouble_second_exact_intermediate_finiteSystem_of_neg_one_mantissa_mem_upper_branch`, using the `1/4` certificates `FloatingPointFormat.problem2_24_ieeeSingle_one_quarter_finiteSystem` and `FloatingPointFormat.problem2_24_ieeeDouble_one_quarter_finiteSystem` at the upper endpoint, prove that normalized exponent-`-1` mantissas in the corresponding `[upper-neighbor-above-1/3, 3/8]` interval have finite exact second intermediates.  The interval-to-mantissa adapters `FloatingPointFormat.problem2_24_ieeeSingle_finiteSystem_upper_branch_exists_neg_one_mantissa` and `FloatingPointFormat.problem2_24_ieeeDouble_finiteSystem_upper_branch_exists_neg_one_mantissa` now classify finite IEEE values in that explicit upper-neighbor interval, and `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_finiteSystem_upper_branch` plus `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_finiteSystem_upper_branch` force a nonfinite third exact intermediate for any zero branch satisfying the explicit upper-neighbor lower bound.  The adjacent no-gap lemmas `FloatingPointFormat.problem2_24_ieeeSingle_upper_neighbor_le_of_finiteSystem_of_one_third_le` and `FloatingPointFormat.problem2_24_ieeeDouble_upper_neighbor_le_of_finiteSystem_of_one_third_le` move finite inputs at or above `1/3` into that explicit upper-neighbor interval, so `FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_implies_third_exact_intermediate_nonfinite` and `FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_implies_third_exact_intermediate_nonfinite` prove that every modeled finite IEEE zero branch has a nonfinite third exact real intermediate.  The remaining generic modeled finite-input branch is therefore `[3/10, 5/12]`; after adjacent-value specialization, the remaining IEEE single/double modeled branch has exact final cancellation and a third-exact-intermediate failure, with the next missing bridge being the contradiction/representability theorem for that third exact intermediate on the localized zero branch, plus the full-IEEE special-value/flag lift.

Problem 2.25 Kahan FMA determinant update: `problem2_25_fmaCore_eq_det2x2` formalizes the exact algebra behind the source algorithm for `det [[a,b],[c,d]] = a*d - b*c`: for any rounded-product placeholder `w`, the exact FMA residual core `(a*d-w) + (w-b*c)` equals the determinant.  `problem2_25_finiteFmaCorrection_eq_exact_of_finiteSystem` and `problem2_25_finiteFmaMain_eq_exact_of_finiteSystem` package the finite round-to-even FMA exactness obligations for the two residuals, and `problem2_25_finiteFmaCore_eq_det2x2_of_exact_residuals` proves that, once those residuals are representable, the finite FMA core is exact.  `problem2_25_finiteFmaDet_signedRelErrorWitness_lt` and `problem2_25_finiteFmaDet_relError_lt_unitRoundoff` then give the final finite-normal relative-error theorem: the rounded determinant has relative error strictly below `unitRoundoff`.  `problem2_25_finiteRoundedProduct`, `problem2_25_finiteFmaDetWithRoundedProduct`, and `problem2_25_finiteRoundedProduct_finiteSystem` now wire in the source's first computed quantity `w = fl(b*c)` and prove it is finite in the model; `problem2_25_roundedProductResidualsRepresentable` names the exact-residual representability side condition for that rounded product.  `problem2_25_finiteFmaDetWithRoundedProduct_signedRelErrorWitness_lt`, `problem2_25_finiteFmaDetWithRoundedProduct_relError_lt_unitRoundoff`, and `problem2_25_finiteFmaDetWithRoundedProduct_highRelativeAccuracy` specialize and package the same signed-witness and relative-error theorem for the displayed rounded-product algorithm.  Remaining Problem 2.25 scope is the binary/IEEE proof that the residual representability hypotheses hold for the intended floating-point input class, plus full IEEE FMA/addition semantics with flags, traps, signed zeros, infinities, NaNs, and payload behavior.

Problem 2.26 reciprocal Newton update: `reciprocalNewtonCorrection_eq_step`, `reciprocalNewtonStep_residual_sq`, `reciprocalNewtonStep_error_sq`, and `reciprocalNewtonStep_fixed_point` close the exact real-arithmetic derivation for Newton's method on `f(x) = a - 1/x = 0`.  For `x != 0`, the literal Newton correction simplifies to `x_next = x*(2 - a*x)`; the residual squares as `1 - a*x_next = (1 - a*x)^2`; and for `a != 0`, the reciprocal error satisfies `1/a - x_next = (1/a)*(1 - a*x)^2`, with `1/a` as a fixed point.  `reciprocalNewtonStepIter_residual_pow_two` lifts the exact result to stored exact iterates, proving `1 - a*x_n = (1-a*x_0)^(2^n)`.  `division_eq_multiply_by_reciprocal`, `divisionViaReciprocal_error_eq_residual`, `reciprocalNewtonStep_division_error_sq`, and `reciprocalNewtonStepIter_division_error_pow_two` now formalize the source sentence that division is implemented as `num/denom = num*(1/denom)`: the reciprocal residual directly scales the division error, and exact Newton iterates give the doubled-exponent division-error law.  The rounded-step surface is now started: `reciprocalNewtonRoundedStep_eq_errorEval` and `reciprocalNewtonRoundedResidual_eq_errorEval` expose the three local standard-model errors from `a*x`, `2-fl(a*x)`, and the final product by `x`.  `reciprocalNewtonRoundedResidual_eq_residualErrorEval` then rewrites the rounded residual as a range-free recurrence in the incoming exact residual `1-a*x`, and `reciprocalNewtonRoundedResidualErrorEval_zero_errors` proves that the recurrence collapses to the exact square when the local errors are zero.  `reciprocalNewtonRoundedResidualErrorEval_eq_sq_plus_roundoff` decomposes the rounded recurrence into the ideal Newton square plus the three local-error perturbations, while `reciprocalNewtonRoundedResidualErrorEval_abs_le` proves the conservative one-step bound `reciprocalNewtonRoundedResidualAbsBound` assuming each local error is bounded by `u`.  The readability layer `reciprocalNewtonRoundedResidualAbsBound_le_radius`, `reciprocalNewtonRoundedResidualAbsBound_le_small_radius`, `reciprocalNewtonRoundedResidualErrorEval_abs_le_small_radius`, and `reciprocalNewtonRoundedResidual_abs_le_small_radius` packages this as the one-step estimate `|r_next| <= rho^2 + 22*u` under `|r| <= rho <= 1` and `u <= 1`, including the concrete rounded residual trace.  `reciprocalNewtonRoundedResidualErrorEval_abs_le_self_radius` and `reciprocalNewtonRoundedResidual_abs_le_self_radius` add the one-step small-ball invariant `|r_next| <= rho` under `rho <= 1/2` and `44*u <= rho`; `reciprocalNewtonRoundedResidualErrorEvalIter_abs_le_self_radius` lifts that invariant to every finite iterate of `reciprocalNewtonRoundedResidualErrorEvalIter` under uniformly bounded local errors.  `reciprocalNewtonRoundedResidualEnvelope` and `reciprocalNewtonRoundedResidualErrorEvalIter_abs_le_envelope` give the scalar envelope recurrence `E_{n+1}=E_n^2+22*u` and prove every finite rounded-residual iterate is bounded by it.  The envelope-side-condition theorems `reciprocalNewtonRoundedResidualEnvelope_nonneg`, `reciprocalNewtonRoundedResidualEnvelope_le_self_radius`, and `reciprocalNewtonRoundedResidualErrorEvalIter_abs_le_envelope_of_self_radius` prove the needed envelope nonnegativity and `[0,1]` side conditions from the source-shaped assumptions `rho <= 1/2` and `44*u <= rho`.  The explicit floor corollaries `reciprocalNewtonRoundedResidualEnvelope_le_roundoff_floor` and `reciprocalNewtonRoundedResidualErrorEvalIter_abs_le_roundoff_floor` prove that starting inside `44*u` keeps the scalar envelope and every finite rounded-residual iterate below the roundoff floor `44*u` when `u <= 1/88`.  The closed-form rate corollaries `reciprocalNewtonRoundedResidualEnvelope_le_geometric_floor` and `reciprocalNewtonRoundedResidualErrorEvalIter_abs_le_geometric_floor` prove the readable geometric-plus-floor bound `rho/2^n + 44*u` for the scalar envelope and every finite standard-model residual iterate.  `reciprocalNewtonRoundedStepIter` defines the actual stored rounded trace, and `reciprocalNewtonRoundedStepIter_residual_abs_le_envelope_of_self_radius`, `reciprocalNewtonRoundedStepIter_residual_abs_le_geometric_floor`, and `reciprocalNewtonRoundedStepIter_residual_abs_le_roundoff_floor` prove that its stored residuals inherit the same envelope, geometric-plus-floor, and `44*u` floor bounds; `reciprocalNewtonRoundedStepIter_division_error_abs_le_geometric_floor` and `reciprocalNewtonRoundedStepIter_division_error_abs_le_roundoff_floor` convert those stored-residual bounds into absolute division-error bounds scaled by `|num/denom|`.  `FloatingPointFormat.reciprocalNewtonFiniteStep_eq_step_of_finiteSystem`, `FloatingPointFormat.reciprocalNewtonFiniteStep_residual_sq_of_finiteSystem`, and `FloatingPointFormat.reciprocalNewtonFiniteStep_error_sq_of_finiteSystem` prove that the concrete finite round-to-even trace agrees with the exact step and inherits the squared identities whenever `a*x`, `2-a*x`, and `x*(2-a*x)` are finite representable.  `FloatingPointFormat.reciprocalNewtonFiniteStepIter_residual_sq_of_finiteSystem`, `FloatingPointFormat.reciprocalNewtonFiniteStepIter_residual_pow_two_of_finiteSystem`, `FloatingPointFormat.reciprocalNewtonFiniteStepIter_error_pow_two_of_finiteSystem`, and `FloatingPointFormat.reciprocalNewtonFiniteStepIter_division_error_pow_two_of_finiteSystem` instantiate this for stored finite iterates under the corresponding per-step exact-intermediate finiteness hypotheses, including the doubled-exponent residual, reciprocal-error, and division-error laws.  Remaining Problem 2.26 scope is full IEEE exceptional-value behavior.

Problem 2.27 residual convergence-test update: `problem2_27_residual_eq_zero_iff_fullAccuracy` proves that exact residual zero for `x - y*z` is equivalent to `y*z = x`, and `problem2_27_fullAccuracy_iff_eq_div` turns this into `z = x/y` when `y != 0`.  `FloatingPointFormat.problem2_27_convergenceTest_iff_fullAccuracy_of_exact_residual_path` proves that the concrete finite round-to-even residual test `fl(x - fl(y*z)) = 0` is equivalent to full accuracy when both the product and residual path are finite-system exact.  The (2.8) theorem surface includes `FloatingPointFormat.problem2_27_convergenceTest_fullAccuracy_of_additive_model_normal_branch`, `FloatingPointFormat.problem2_27_convergenceTest_of_fullAccuracy_additive_model_normal_branch`, and `FloatingPointFormat.problem2_27_convergenceTest_iff_fullAccuracy_of_additive_model_normal_branch`: in the normal branch where the additive underflow term is zero, the zero computed-residual test is equivalent to full accuracy.  `FloatingPointFormat.problem2_27_convergenceTest_fullAccuracy_or_underflow_bound_of_additive_model` records the unavoidable gradual-underflow ambiguity: without the normal-branch condition, the exact residual may merely lie within the eta-bound; `FloatingPointFormat.problem2_27_convergenceTest_fullAccuracy_or_strict_underflow_bound_of_strict_model` gives the corresponding strict eta-bound under the strict no-half-tie model.  The division-form wrappers `FloatingPointFormat.problem2_27_convergenceTest_eq_div_of_additive_model_normal_branch`, `FloatingPointFormat.problem2_27_convergenceTest_iff_eq_div_of_additive_model_normal_branch`, `FloatingPointFormat.problem2_27_convergenceTest_eq_div_or_underflow_bound_of_additive_model`, and `FloatingPointFormat.problem2_27_convergenceTest_eq_div_or_strict_underflow_bound_of_strict_model` state the source quotient conclusion directly for `y != 0`: the normal branch is equivalent to `z = x/y`, the general additive model certifies either `z = x/y` or an eta-small exact residual, and the strict model sharpens that residual alternative to a strict eta-bound.  Remaining Problem 2.27 scope is a concrete full IEEE division-iteration trace with flags/traps/special values, not the source residual convergence-test argument.

Problem 2.3 interval-classifier and branch-family no-extra update: `problem2_3_sameExponentInteriorDoubleMantissas_mem_iff`, `problem2_3_boundaryInteriorDoubleMantissas_mem_iff`, `problem2_3_subnormalBlockInteriorDoubleMantissas_mem_iff`, and `problem2_3_smallestSubnormalInteriorDoubleMantissas_mem_iff` identify the listed strict interior mantissa intervals exactly by their scaled integer bounds.  The classifiers `problem2_3_ieeeDouble_sameExponent_between_iff_mem`, `problem2_3_ieeeDouble_sameExponent_negative_between_iff_mem`, `problem2_3_ieeeDouble_boundary_between_iff_mem`, `problem2_3_ieeeDouble_boundary_negative_between_iff_mem`, `problem2_3_ieeeDouble_subnormalBlock_between_iff_mem`, and `problem2_3_ieeeDouble_subnormalBlock_negative_between_iff_mem` prove that, in the signed same-exponent, signed exponent-boundary, and signed subnormal-block branches, the real strict-between predicate is equivalent to membership in the listed interval.  The reverse lemmas `problem2_3_ieeeDouble_normalized_sameExponent_signed_between_mem`, `problem2_3_ieeeDouble_finiteSystem_sameExponent_signed_between_exists_mem`, `problem2_3_ieeeDouble_normalized_boundary_signed_between_mem`, `problem2_3_ieeeDouble_finiteSystem_boundary_signed_between_exists_mem`, `problem2_3_ieeeDouble_normalized_subnormalBlock_signed_between_mem`, and `problem2_3_ieeeDouble_finiteSystem_subnormalBlock_signed_between_exists_mem` close finite-system no-extra classification for the signed same-exponent, signed exponent-boundary, and signed subnormal-block branches, including zero/subnormal or wrong-binade exclusion.  The single branch-family formulation `Problem2_3IeeeSingleAdjacentGap`, with `problem2_3_adjacentSingleGapInteriorDoubleMantissas_card`, `problem2_3_adjacentSingleGap_between_iff_mem`, `problem2_3_adjacentSingleGapDoubleValue_finiteSystem_of_mem`, and `problem2_3_adjacentSingleGap_finiteSystem_between_exists_mem`, now packages those signed branches under one count/classifier/finite/no-extra theorem surface.  The source-facing endpoint coverage theorems `problem2_3_exists_adjacentSingleGap_of_ieeeSingle_subnormalMantissa`, `problem2_3_exists_adjacentSingleGap_of_ieeeSingle_realOrderAdjacentNormalized_ordered`, and `problem2_3_exists_adjacentSingleGap_of_ieeeSingle_realOrderAdjacentNormalized` connect arbitrary signed subnormal grid steps and arbitrary finite normalized real-order adjacent endpoint pairs to the same branch-family constructors.  This closes the currently stated Problem 2.3 branch-family exactness and endpoint-coverage surface.

Problem 2.3 status note: older C2.21 or not-proved-ledger shorthand saying that Problem 2.3 no-extra exactness or normalized-endpoint coverage remains open is stale.  The signed same-exponent, signed exponent-boundary, signed subnormal-block, combined branch-family finite-system no-extra, arbitrary signed subnormal-grid coverage, and finite normalized real-order adjacent endpoint coverage theorems above are closed.

Problem 2.7 finite-normal selector update: `sourceRoundToEvenEvidence_unique` and `finiteNormalRoundToEven_eq_of_sourceRoundToEvenEvidence` now prove that source round-to-even evidence uniquely determines the finite-normal selector output, including exact representable inputs, endpoint brackets, strict-nearer branches, and half-tie parity branches.  Older shorthand saying that the finite-normal selector uniqueness gap remains open is stale.  The sign-symmetry and total finite round-to-even oddness lift is now closed by the follow-up update below.

Problem 2.7 local and finite sign-symmetry update: `realOrderAdjacentNormalized_neg_ordered` proves that negating an ordered adjacent normalized bracket reverses it as `(-b,-a)`, and `nearestAdjacentRoundToEven_neg_of_even_right_iff_not_even_left` proves the local round-to-even selector is odd whenever the reversed bracket's left mantissa has parity opposite to the original left mantissa.  The same-exponent parity flip is closed by `evenMantissa_succ_iff_not_evenMantissa` and `evenMantissa_iff_not_evenMantissa_succ`; the exponent-boundary parity flip is closed under the IEEE/binary-style side conditions that the base is even and `1 < t` by the `evenMantissa_minNormalMantissa_*`, `evenMantissa_maxNormalMantissa_*`, and `not_evenMantissa_maxNormalMantissa_*` lemmas.  `realOrderAdjacentNormalized_right_mantissa_parity`, `sourceRoundToEvenEvidence_neg`, `finiteNormalRoundToEven_neg`, `finiteRoundToEven_neg_of_finiteNormalRange`, `finiteRoundToEven_neg`, and `problem2_7_statement2_sub_sign_symmetry` now close the source-evidence sign symmetry, finite-normal selector oddness, total finite selector oddness, and Problem 2.7 statement 2 under those explicit side conditions.  Full IEEE operation semantics with special values, flags, traps, and signed-zero behavior remain open.

Problem 2.7 stale-summary note: older table or priority-row shorthand saying that the remaining unrestricted Problem 2.7 gap is finite-normal total-selector oddness/uniqueness is stale.  At the finite-selector layer, the subtraction sign-symmetry result is closed by `problem2_7_statement2_sub_sign_symmetry` under even radix and `1 < t`; the remaining work is the full IEEE operation-semantics lift.

Problem 2.8 guard-digit audit update: `problem2_8_finiteRoundToEven_guarded_sequence_counterexample` proves that the naive finite round-to-even operation-sequence interpretation of `fl(a+(b-a)/2)` is not implied by exact subtraction alone.  In the one-digit decimal format with `1/2` representable, `2-1` and division by `2` are exact, but the final rounded addition `1+1/2` returns the endpoint `2`, so `1 < fl(1+(2-1)/2) < 2` fails for that interpretation.  `decimalOneDigitThreeExponentFormat_three_halves_not_finiteSystem` and `problem2_8_guarded_sequence_counterexample_missing_midpoint_finiteSystem` prove that this same witness fails exactly the final-midpoint representability hypothesis: `1+(2-1)/2 = 3/2` is not finite in the chosen format, even though `2-1` and `(2-1)/2` are finite.  The exact real core `problem2_8_exact_guarded_midpoint_strict_between` proves `a < a+(b-a)/2 < b` from `a < b`.  The source-shaped exact-operation wrappers `problem2_8_guarded_exact_operation_sequence_eq_exact_midpoint` and `problem2_8_guarded_exact_operation_sequence_strict_between` prove that any operation model returning exact subtraction, exact halving, and exact final addition computes this interior midpoint.  The finite-selector bridge `problem2_8_guarded_sequence_eq_exact_midpoint_of_finite_midpoint_steps` proves the rounded operation sequence equals the same midpoint if the exact subtraction `b-a`, exact half-difference `(b-a)/2`, and final midpoint `a+(b-a)/2` are all finite representable, and `problem2_8_guarded_sequence_strict_between_of_finite_midpoint_steps` then gives the strict inequality under those visible hypotheses.  `problem2_8_guarded_sequence_strict_between_of_sterbenz_subtraction` discharges the exact-subtraction hypothesis from finite endpoints plus Sterbenz's ratio condition, leaving the half-difference and final-midpoint representability hypotheses explicit.  The remaining Problem 2.8 gap is tying a concrete full guard-digit/IEEE operation implementation to the exact-step model, not the real-arithmetic interior-midpoint conclusion itself.

## Hidden-Hypothesis Audit

- `FloatingPointFormat` is a finite-format vocabulary plus first range/spacing
  foundation.  It now proves the normalized global endpoint range across
  `emin`/`emax` and the positional digit-string equivalence for integer
  mantissas, source-facing finite normal/underflow/overflow range predicates,
  finite-system range/non-overflow classification, finite nearest-rounding
  output range/non-overflow/magnitude classification, relation-level signed
  overflow saturation to the largest finite endpoints, smallest-subnormal
  lower-bound facts, relation-level tiny-input underflow-to-zero, the
  positive/negative finite-normal-range output bridges, the non-strict and
  strict finite-normal-range Theorem 2.2 relation theorems, the arbitrary-output
  strict theorem `nearestRoundingToFinite_signedRelErrorWitness_lt_of_finiteNormalRange`,
  the source-choice theorem `finiteNormalFl_signedRelErrorWitness_lt`, the
  finite-normal-range Theorem 2.3 inverse relation theorem, and the arbitrary
  finite-normal source-choice theorem `finiteNormalFl_inverseRelErrorWitness`,
  plus uniqueness of
  signed normalized `(m,e)` representations as real values.  It now proves
  source-facing overflow saturation by `finiteOverflowSaturation`,
  finite-underflow output classification into zero/subnormal cases, finite
  representable sign symmetry by `finiteSystem_neg`, finite nearest-rounding
  sign symmetry by `nearestRoundingToFinite_neg`, relation-level finite
  underflow nearest existence by
  `exists_nearestRoundingToFinite_finiteUnderflowRange`, global finite nearest
  existence by `exists_nearestRoundingToFinite`, and the total arbitrary finite
  nearest choice `finiteNearestFl`.  It also proves the source-facing finite
  round-away selector `finiteRoundAway`, including its underflow, normal, and
  overflow branches, plus the source-facing finite round-to-even selector
  `finiteRoundToEven`, built from `nearestAdjacentRoundToEven`,
  `finiteNormalRoundToEven`, underflow tie-to-even, and overflow saturation.
  It also proves the ordinary finite operation wrappers `finiteRoundToEvenOp`
  and `finiteRoundToEvenSqrt`, deriving the strict standard-model equation for
  primitive exact real operations and square root when the exact result is
  finite-normal, and exactness when that exact result is finite representable.
  The finite left-add-zero side condition is closed by
  `finiteRoundToEvenOp_add_zero_of_finiteSystem`.  `IeeeRoundingMode`,
  `IeeeExceptionFlag`, `IeeeValue`, and `IeeeOperationResult` now make the
  future IEEE result space explicit, and the current source-facing finite
  selectors are embedded only through `IeeeOperationResult.finiteNoFlags`.
  `ieeeOverflowValue`, `ieeeOverflowResult`, `ieeeOverflowDefaultResult`,
  `ieeeUnderflowResult`, `ieeeUnderflowDefaultResult`,
  `ieeeUnderflowModeRoundingEvidence`, `ieeeUnderflowModeResult`,
  `ieeeInvalidOperationResult`, `ieeeInvalidOperationDefaultResult`,
  `ieeeSqrtInvalidResult`, `ieeeSqrtInvalidDefaultResult`,
  `ieeeSqrtSpecialValueResult`, and `IeeeOperationResult.valueNoFlags` now give
  the first flagged overflow/underflow/invalid-operation and flag-free
  non-finite result semantics over this result space.
  `ieeeRoundToNearestEvenOpResult` dispatches primitive-operation overflow
  exact results to the flagged overflow result, underflow exact results to the
  flagged finite underflow result, and ordinary non-overflow/non-underflow
  results to the finite/no-flags operation wrapper.
  `ieeeRoundToModeOpResult` generalizes this primitive-operation result
  dispatch over `IeeeRoundingMode`, proving mode-dependent overflow results
  for nearest/even, toward-zero, toward-positive, and toward-negative modes
  through `ieeeOverflowValue`, plus the corresponding mode-aware underflow and
  ordinary finite/no-flags branches through `finiteRoundToModeOp`; the square-root
  mode wrapper provides the same finite-branch dispatch through
  `finiteRoundToModeSqrt`.
  `ieeeRoundToNearestEvenSqrtResult` dispatches nonnegative real square-root
  overflow exact results to the flagged overflow result, underflow exact
  results to the flagged finite underflow result, and ordinary
  non-overflow/non-underflow results to the finite/no-flags square-root wrapper.
  It dispatches negative real square-root inputs to the NaN/invalid-operation
  result.  `ieeeRoundToNearestEvenSqrtValueResult` dispatches NaN input to NaN
  with no flags, positive infinity to positive infinity with no flags, and
  negative infinity to the NaN/invalid-operation result.  It also dispatches
  positive zero to positive zero and negative zero to negative zero with no
  flags.
  `finiteOverflowSaturationIeeeFiniteResult_not_ieeeOverflowResult` records
  that finite saturation is not IEEE overflow/infinity/flag semantics.  The
  additive underflow
  model (2.8) now has visible algebraic predicates
  `additiveUnderflowModelWitness` and
  `strictAdditiveUnderflowModelWitness`, visible gradual/flush eta-bound
  constants, and a proved identity that `u * alpha` is half the subnormal
  spacing.  It does not yet prove uniqueness under a concrete IEEE operation
  tie rule, traps, directed rounding operation behavior, signaling-NaN/payload
  behavior, remaining special-value propagation beyond the first primitive/square-root
  predicate branches, or a total IEEE operation
  semantics.  Structural
  adjacency and real-order adjacency are now connected in both directions for
  normalized values, and
  `realOrderAdjacentNormalized_spacing_bounds_left` proves the Lemma 2.1
  relative-spacing inequality over the real-order target.  Exact normalized
  inputs now round to themselves with the signed witness `delta = 0`.  The
  adjacent-bracket nearest-rounding theorems prove the local endpoint choice,
  half-gap and unit-roundoff bounds, and package them as signed relative-error
  witnesses once adjacent normalized bracketing endpoints are supplied.  The
  floor-based same-exponent theorems now construct such endpoints and the
  nearest-rounding signed witness for signed inputs once the source exponent
  bin is already known; the power-interval and boundary-gap adapters are
  combined by signed power-slice wrappers over `beta^(e-1) <= x <= beta^e`
  and its negative counterpart.  `exists_powerSliceExponent_positive`/`negative`
  remove the global exponent-selection hypothesis for nonzero inputs into
  unbounded `G`, and
  `exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_nonzero` packages
  the resulting strict signed relative-error witness and
  computed-denominator witness.  `exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_nonzero`
  carries the explicit local round-away selector evidence through the same
  global nonzero source-level bridge, and `finiteNormalRoundAway` packages that evidence
  into a finite-normal source choice.  `sourceRoundToEvenEvidence` and
  `finiteNormalRoundToEven` now do the same for the local tie-to-even selector
  on finite-normal inputs, including the strict signed witness and inverse
  witness.  `finiteOverflowSaturation` packages the
  signed largest-finite endpoint and proves nearest-rounding existence and
  uniqueness for source-facing overflow-range inputs.  The finite underflow
  classifier now proves that finite underflow-range outputs are exactly zero
  or subnormal, and nonzero finite underflow outputs are subnormal.  The
  relation-valued signed subnormal nearest grid is closed by the first-cell
  theorems
  `nearestRoundingToFinite_minSubnormalMagnitude_of_half_le_of_le_three_halves`
  and
  `nearestRoundingToFinite_neg_minSubnormalMagnitude_of_neg_three_halves_le_of_le_neg_half`,
  and by the general grid-cell theorems
  `nearestRoundingToFinite_subnormalValue_false_of_half_cell` and
  `nearestRoundingToFinite_subnormalValue_true_of_half_cell`.
  The finite zero
  relation case is closed by
  `exists_nearestRoundingToFinite_signedRelErrorWitness_zero`, and tiny-input
  finite relation rounding is closed up to and below the half-smallest-subnormal
  threshold by `nearestRoundingToFinite_zero_of_abs_le_half_minSubnormalMagnitude`
  and `nearestRoundingToFinite_eq_zero_of_abs_lt_half_minSubnormalMagnitude`.
  The smallest-normal boundary cell is closed by
  `nearestRoundingToFinite_minNormalMagnitude_of_subnormal_boundary_half_le`
  and
  `nearestRoundingToFinite_neg_minNormalMagnitude_of_subnormal_boundary_half_le`;
  the middle subnormal underflow selector is closed by
  `exists_nearestRoundingToFinite_positive_subnormal_middle`; and the full
  relation-level finite-underflow/global existence layer is closed by
  `exists_nearestRoundingToFinite_finiteUnderflowRange`,
  `exists_nearestRoundingToFinite`, and `finiteNearestFl`; the source-facing
  round-away layer is closed by `finiteUnderflowRoundAway` and
  `finiteRoundAway`, and the source-facing round-to-even layer is closed by
  `nearestAdjacentRoundToEven`, `finiteNormalRoundToEven`,
  `finiteUnderflowRoundToEven`, and `finiteRoundToEven`; the local adjacent
  directed endpoint layer is closed by `adjacentRoundTowardNegative`,
  `adjacentRoundTowardPositive`, and `adjacentRoundTowardZero`, with
  exact endpoint preservation, representability, and one-sided/order facts, and
  the finite-normal directed layer is closed by
  `finiteNormalRoundTowardNegative`, `finiteNormalRoundTowardPositive`, and
  `finiteNormalRoundTowardZero`; the ordinary
  finite-normal and exact finite-representable operation bridge is closed by
  `finiteRoundToEvenOp` and `finiteRoundToEvenSqrt`; and the finite-normal
  no-underflow branch of (2.8) is closed by the strict additive-underflow
  normal-branch wrappers, while the gradual-underflow branch is closed by the
  finite nearest/output absolute-error theorems and additive underflow branch
  wrappers, with strict variants under `finiteUnderflowNoHalfTie`; and the
  finite directed selector layer is closed by `finiteRoundTowardNegative`,
  `finiteRoundTowardPositive`, `finiteRoundTowardZero`, and
  `finiteRoundToMode`, and the primitive-operation and square-root IEEE mode wrappers
  now dispatch finite underflow/no-flag branches through `finiteRoundToModeOp`
  and `finiteRoundToModeSqrt`.  The
  remaining hidden hypotheses are trap handling, full directed-mode
  operation semantics beyond primitive/square-root finite branches,
  signaling-NaN/payload behavior, remaining
  infinity/special-value propagation beyond the first primitive/square-root predicate
  branches, and an
  explicit IEEE operation tie rule.
- `FPModel` is an abstract axiomatic model.  It does not assert IEEE formats,
  exact rounding, subnormals, exception flags, signed zeros, infinities, NaNs,
  monotonicity, or overflow/underflow behavior.
- Local `FPModel` still uses `|delta| <= u` for primitive operations.  The
  finite-format relation theorem for normal-range nearest rounding now proves
  Higham's strict `|delta| < u` source form, but this has not been pushed back
  into `FPModel` as an operation-level axiom.
- The new inverse-model theorem requires nonzero exact and computed values for
  the equivalence with computed-denominator relative error.
- The finite-format source theorems cannot be marked closed by `FPModel`,
  because `FPModel` assumes operation-level error bounds instead of deriving
  them from a number system and rounding rule.

## Next Frontier Target

The highest-leverage next theorem is now a full IEEE operation-semantics step
beyond the primitive real-valued finite branch.  The source-facing finite
round-to-even/op/sqrt bridge covers finite-normal relative error, exact finite
representable results, non-strict gradual underflow, strict no-half-tie gradual
underflow, finite flag-free embeddings, flagged overflow/underflow/invalid-
operation default results, nearest/even and mode-parameterized primitive-
operation overflow/underflow dispatch, square-root negative/overflow/underflow
dispatch, square-root signed-zero preservation, and square-root NaN/positive-
infinity/negative-infinity special-value branches.  The local adjacent directed
selectors now provide exact endpoint-preserving choices and one-sided/order
facts for an ordered adjacent normalized bracket, the finite-normal directed
selectors lift those choices through source exponent-slice evidence, and the
total finite directed selectors combine those normal branches with
subnormal-lattice underflow branches and finite overflow saturation.  The
mode-aware primitive-operation and square-root wrappers now dispatch finite
underflow/no-flag branches to `finiteRoundToModeOp` and
`finiteRoundToModeSqrt`.

1. Extend the IEEE result wrapper toward concrete operations: add the next
   special-value/trap branch family, or prove directed-mode additive-underflow
   bounds if the next Chapter 2 proof target stays within real finite operations.
