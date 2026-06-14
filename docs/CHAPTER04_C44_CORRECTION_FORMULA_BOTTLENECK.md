# Chapter 4.4 Correction Formula Bottleneck

## Source Target

Higham Chapter 4, pp. 92--93, equation (4.7), states that for floating-point
numbers `a` and `b` with `|a| > |b|`, if `s = fl(a+b)` and
`e = fl((a-s)+b)` are evaluated in the displayed parenthesized order, then in
rounded base-2 arithmetic

```text
a + b = s + e.
```

The source cites Dekker 1971 Theorem 4.7, Knuth 1981 Theorem C, and
Linnainmaa 1974 Theorem 3 for the full base-2 result.

## Current Lean Surface

The executable/source trace is closed by:

- `CorrectionFormulaTrace`
- `CorrectionFormulaTrace.exact`
- `correctionFormulaTrace`
- `finiteCorrectionFormulaTrace`

The current finite-format exactness routes are closed by:

- `finiteCorrectionFormulaTrace_exact_of_exact_sub_and_finite_error_add`
- `finiteCorrectionFormulaTrace_exact_of_sterbenz_and_finite_error_add`
- `finiteCorrectionFormulaTrace_exact_of_signed_sterbenz_and_finite_error_add`
- `finiteCorrectionFormulaTrace_exact_of_two_signed_sterbenz`
- `FastTwoSumFiniteCertificate`
- `FastTwoSumFiniteCertificate.finite_s_unconditional`
- `FastTwoSumFiniteCertificate.of_error_obligations`
- `FastTwoSumFiniteCertificate.finite_error_of_sameExponentScaledInteger`
- `FastTwoSumFiniteCertificate.of_two_signed_sterbenz`
- `correctionFormula_abs_order_not_imply_signed_sterbenz_exact_sum`
- `FastTwoSumFiniteCertificate.of_exact_add`
- `finiteCorrectionFormulaTrace_exact_of_fastTwoSumFiniteCertificate`
- `finiteCorrectionFormulaTrace_exact_of_exact_add`
- `FloatingPointFormat.normalizedValue_add_sameSign_sameExponent_eq_scaledInteger`
- `FloatingPointFormat.normalizedMantissa_add_lt_two_mul_mantissaBound`
- `FloatingPointFormat.normalizedValue_add_sameSign_sameExponent_exists_scaledIntegerCoeff`
- `FloatingPointFormat.normalizedValue_add_sameSign_sameExponent_finiteSystem_of_add_lt_mantissaBound`
- `FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_sameExponent_eq_exact_of_add_lt_mantissaBound`
- `FloatingPointFormat.finiteRoundToEvenOp_add_error_finite_of_sourceRoundToEvenEvidence`
- `FloatingPointFormat.binaryGuardCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_ceil`
- `FloatingPointFormat.normalizedValue_succExponent_eq_beta_scaledInteger`
- `FloatingPointFormat.normalizedValue_add_twoExponent_eq_beta_sq_scaledInteger`
- `FloatingPointFormat.binaryGuardSource_between_sameExponentEndpoints_positive`
- `FloatingPointFormat.binaryGuardSource_between_sameExponentEndpoints_negative`
- `FloatingPointFormat.binaryGuardSource_between_boundaryEndpoints_positive`
- `FloatingPointFormat.binaryGuardSource_between_boundaryEndpoints_negative`
- `FloatingPointFormat.binaryGuardQuotient_normalized_or_max_of_mantissaBound_le_of_lt_two_mul`
- `FloatingPointFormat.binaryGuardBoundaryCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_boundary`
- `FloatingPointFormat.sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between`
- `FloatingPointFormat.sourceRoundToEvenEvidence_sameExponent_mantissa_eq_or_succ_of_bracket`
- `FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_mantissa_eq_or_succ_of_bracket`
- `FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_coeffDiff_natAbs_lt_mantissaBound`
- `FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_mantissa_eq_or_succ_of_bracket`
- `FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_coeffDiff_natAbs_lt_mantissaBound`
- `FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem`
- `FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem`
- `FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem_of_normalizedQuotient`
- `FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem_of_normalizedQuotient`
- `FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem_of_guardCoeffBounds`
- `FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem_of_guardCoeffBounds`
- `FloatingPointFormat.sourceRoundToEvenEvidence_positive_normalizedValue_add_sameSign_sameExponent_error_finiteSystem`
- `FloatingPointFormat.sourceRoundToEvenEvidence_negative_normalizedValue_add_sameSign_sameExponent_error_finiteSystem`
- `FloatingPointFormat.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_sameExponent_error_finiteSystem`
- `FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_sameExponent_error_finiteSystem`
- `FloatingPointFormat.finiteRoundToEvenOp_add_oppositeSign_sameExponent_eq_exact`
- `FloatingPointFormat.finiteRoundToEvenOp_add_oppositeSign_sameExponent_error_finiteSystem`
- `FloatingPointFormat.finiteRoundToEvenOp_add_neg_right_normalizedSystem_eq_exact_of_sterbenzRatioCondition`
- `FloatingPointFormat.finiteRoundToEvenOp_add_neg_right_normalizedSystem_error_finiteSystem_of_sterbenzRatioCondition`
- `FloatingPointFormat.finiteRoundToEvenOp_add_neg_right_positive_normalizedValue_eq_exact_of_sterbenzRatioCondition`
- `FloatingPointFormat.finiteRoundToEvenOp_add_neg_right_positive_normalizedValue_error_finiteSystem_of_sterbenzRatioCondition`
- `FloatingPointFormat.finiteRoundToEvenOp_add_neg_right_finiteSystem_eq_exact_of_sterbenzRatioCondition`
- `FloatingPointFormat.finiteRoundToEvenOp_add_neg_right_finiteSystem_error_finiteSystem_of_sterbenzRatioCondition`
- `FloatingPointFormat.finiteRoundToEvenOp_add_neg_left_finiteSystem_eq_exact_of_sterbenzRatioCondition`
- `FloatingPointFormat.finiteRoundToEvenOp_add_neg_left_finiteSystem_error_finiteSystem_of_sterbenzRatioCondition`
- `FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_boundary_eq_max_or_min`
- `FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_boundary_coeffDiff_natAbs_lt_mantissaBound`
- `FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_boundary_eq_max_or_min`
- `FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_boundary_coeffDiff_natAbs_lt_mantissaBound`
- `FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_boundary_error_finiteSystem`
- `FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_boundary_error_finiteSystem`

The abstract-standard-model route is ruled out by:

- `correctionFormulaAbstractCounterexampleFPModel`
- `correctionFormulaAbstractCounterexample_abs_order`
- `correctionFormulaAbstractCounterexample_not_exact`

## Dependency Checklist

| Dependency | Status | Lean evidence / next target |
|---|---|---|
| Source-level rounded trace and exactness predicate | closed | `CorrectionFormulaTrace`, `correctionFormulaTrace`, `CorrectionFormulaTrace.exact` |
| Concrete finite round-to-even trace | closed | `finiteCorrectionFormulaTrace`, `finiteCorrectionFormulaTrace_s`, `finiteCorrectionFormulaTrace_e` |
| Exactness from exact intermediate subtraction and representable local error | closed | `finiteCorrectionFormulaTrace_exact_of_exact_sub_and_finite_error_add` |
| Positive finite-system Sterbenz route for `a-s` | closed | `finiteCorrectionFormulaTrace_exact_of_sterbenz_and_finite_error_add` |
| Signed finite-system Sterbenz route for `a-s` | closed | `finiteCorrectionFormulaTrace_exact_of_signed_sterbenz_and_finite_error_add` |
| Two signed Sterbenz certificates imply full finite certificate | closed | `FastTwoSumFiniteCertificate.of_two_signed_sterbenz` |
| Naive derivation of the `a` versus `a+b` signed Sterbenz branch from `|b| < |a|` | ruled out | `correctionFormula_abs_order_not_imply_signed_sterbenz_exact_sum` gives `a = 1`, `b = -3/4` |
| Rounded sum `s = round(a+b)` is finite | closed | `FastTwoSumFiniteCertificate.finite_s_unconditional`, so future base-2 targets do not need `s` finite as a source hypothesis |
| Certificate construction from the two genuine representability obligations | closed | `FastTwoSumFiniteCertificate.of_error_obligations` packages `a-s` and `(a+b)-s`; `s` finite is automatic |
| Finite certificate implies equation (4.7) | closed | `finiteCorrectionFormulaTrace_exact_of_fastTwoSumFiniteCertificate` |
| Exact first rounded addition implies full finite certificate and equation (4.7) | closed | `FastTwoSumFiniteCertificate.of_exact_add`, `finiteCorrectionFormulaTrace_exact_of_exact_add` |
| Abstract `FPModel` insufficiency | closed | `correctionFormulaAbstractCounterexample_not_exact` |
| Proof-source route for the Dekker/FastTwoSum split | advisory acquired | Shewchuk 1997, Section 2.3, Theorem 6 reproduces Dekker's FAST-TWO-SUM proof; original Dekker/Knuth/Linnainmaa theorem bodies remain unacquired |
| Total finite selector agrees with the finite-normal source selector under source range assumptions | closed | `FloatingPointFormat.finiteRoundToEven_eq_finiteNormalRoundToEven_of_finiteNormalRange`, `FloatingPointFormat.finiteRoundToEvenOp_eq_finiteNormalRoundToEven_of_finiteNormalRange` |
| Finite-normal-range-only shortcut for roundoff-error representability | ruled out | `FloatingPointFormat.finiteNormalRange_not_enough_for_roundoff_error_finiteSystem` gives a binary `t = 2` in-range real `21/16` whose direct roundoff error is `-3/16`, not finite representable; the source theorem must use that the rounded source is an exact addition of finite binary operands |
| Same-exponent coefficient-grid finite error bridge | closed | `FloatingPointFormat.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound` proves that two same-sign values on the same scaled-integer exponent lattice have a finite representable difference whenever the coefficient gap fits in `t` radix digits |
| Coefficient-grid bridge discharges the FastTwoSum `finite_error` field | closed | `FastTwoSumFiniteCertificate.finite_error_of_sameExponentScaledInteger` converts same-lattice source/rounded endpoint representations plus a `t`-digit coefficient gap into `fmt.finiteSystem ((a+b)-fl(a+b))` |
| Aligned same-sign normalized addition source grid | closed | `FloatingPointFormat.normalizedValue_add_sameSign_sameExponent_eq_scaledInteger`, `FloatingPointFormat.normalizedMantissa_add_lt_two_mul_mantissaBound`, and `FloatingPointFormat.normalizedValue_add_sameSign_sameExponent_exists_scaledIntegerCoeff` prove that the exact sum of two same-sign, same-exponent normalized operands is on the common exponent lattice with coefficient `m+n < 2*beta^t`; `FloatingPointFormat.normalizedValue_add_sameSign_sameExponent_finiteSystem_of_add_lt_mantissaBound` and `FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_sameExponent_eq_exact_of_add_lt_mantissaBound` close the aligned exact-first-add branch when `m+n < beta^t` |
| Binary aligned guard-word quotient dispatch | closed | `FloatingPointFormat.binaryGuardQuotient_normalized_or_max_of_mantissaBound_le_of_lt_two_mul` proves that a base-2 coefficient in `[beta^t, 2*beta^t)` decomposed as `k = beta*q+r` either gives an ordinary normalized bracket with `q` and `q+1`, or the lower quotient is exactly `maxNormalMantissa`, forcing the exponent-boundary branch |
| Binary aligned guard-word endpoint coefficient gap | closed | `FloatingPointFormat.binaryGuardCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_ceil` proves that, in base 2, if `k = beta*q + r` and the rounded endpoint coefficient is either `q` or the non-exact upper endpoint `q+1`, then `k - beta*l` has fewer than `t` radix digits |
| Source round-to-even endpoint selection inside a same-exponent adjacent bracket | closed | `FloatingPointFormat.sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between` converts actual source round-to-even evidence plus an ordered adjacent bracket into left/right endpoint selection, and `FloatingPointFormat.sourceRoundToEvenEvidence_sameExponent_mantissa_eq_or_succ_of_bracket` turns same-exponent endpoint representations into the mantissa choice `l = q` or `l = q+1` |
| Positive aligned guard-word quotient bracket and finite local error | closed | `FloatingPointFormat.normalizedValue_succExponent_eq_beta_scaledInteger` shifts the `e+1` endpoint onto the original source lattice, `FloatingPointFormat.binaryGuardSource_between_sameExponentEndpoints_positive` constructs the positive quotient bracket for `k = beta*q+r`, `FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_mantissa_eq_or_succ_of_bracket` excludes the upper endpoint when `r = 0`, `FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_coeffDiff_natAbs_lt_mantissaBound` composes the actual evidence bridge with the binary coefficient-gap lemma, and `FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem` discharges the aligned local roundoff-error finite-system obligation; `FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem_of_normalizedQuotient` removes the separate rounded-endpoint mantissa hypothesis by composing directly from normalized quotient data for `q` and `q+1` |
| Negative aligned guard-word quotient bracket and finite local error | closed | `FloatingPointFormat.binaryGuardSource_between_sameExponentEndpoints_negative` constructs the reversed real-order quotient bracket for the negative same-sign branch, `FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_mantissa_eq_or_succ_of_bracket` handles the reversed endpoint cases and excludes the successor endpoint when `r = 0`, `FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_coeffDiff_natAbs_lt_mantissaBound` composes it with the same binary coefficient-gap lemma, and `FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem` discharges the aligned local roundoff-error finite-system obligation; `FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem_of_normalizedQuotient` removes the separate rounded-endpoint mantissa hypothesis for the reversed real-order branch |
| Exponent-boundary guard-word quotient bracket and finite local error | closed | `FloatingPointFormat.normalizedValue_add_twoExponent_eq_beta_sq_scaledInteger` shifts the next-binade endpoint onto the original source lattice, `FloatingPointFormat.binaryGuardSource_between_boundaryEndpoints_positive` and `FloatingPointFormat.binaryGuardSource_between_boundaryEndpoints_negative` construct the positive and reversed negative boundary brackets, `FloatingPointFormat.binaryGuardBoundaryCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_boundary` proves the base-2 coefficient gap for the max-mantissa/min-next-binade endpoint choice, and the positive/negative boundary source-evidence finite-system wrappers discharge the boundary local roundoff-error obligation |
| Guard coefficient bounds dispatch to ordinary or boundary finite local error | closed | `FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem_of_guardCoeffBounds` and `FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem_of_guardCoeffBounds` compose `FloatingPointFormat.binaryGuardQuotient_normalized_or_max_of_mantissaBound_le_of_lt_two_mul` with the ordinary normalized-quotient wrappers and the boundary finite-error wrappers, so a base-2 guard coefficient in `[beta^t, 2*beta^t)` now directly yields finite local roundoff-error representability for both signs |
| Operand-level aligned same-sign normalized addition finite local error | closed | `FloatingPointFormat.sourceRoundToEvenEvidence_positive_normalizedValue_add_sameSign_sameExponent_error_finiteSystem`, `FloatingPointFormat.sourceRoundToEvenEvidence_negative_normalizedValue_add_sameSign_sameExponent_error_finiteSystem`, and the sign-generic `FloatingPointFormat.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_sameExponent_error_finiteSystem` derive the guard-coefficient hypotheses from actual normalized operands `m,n`, dispatch ordinary/boundary endpoint cases, and prove the source local error finite for aligned same-sign same-exponent binary addition; `FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_sameExponent_error_finiteSystem` transfers the result to the concrete finite-normal rounded-add wrapper |
| Normalized ordered-exponent coefficient-fits exact branch | closed | `FloatingPointFormat.normalizedValue_add_sameSign_orderedExponent_finiteSystem_of_alignedCoeff_lt_mantissaBound` rewrites the high-exponent operand onto the lower exponent lattice and proves finite representability when `mHigh * beta^(eHigh-eLow) + mLow < beta^t`; the two operation-order exact/error wrappers close finite zero local roundoff error for this same-sign normalized different-exponent subcase |
| Normalized ordered-exponent one-guard finite-error branch | closed | `FloatingPointFormat.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_guardCoeffBounds` rewrites the high-exponent operand onto the lower exponent lattice and feeds the aligned coefficient range `beta^t <= k < 2*beta^t` to the existing binary guard dispatcher; `FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_guardCoeffBounds` and its commuted wrapper transfer this source finite-error witness to concrete finite-normal rounded addition |
| Opposite-sign same-exponent normalized addition exact branch | closed | `FloatingPointFormat.finiteRoundToEvenOp_add_oppositeSign_sameExponent_eq_exact` rewrites addition of a flipped-sign operand to same-sign same-exponent subtraction and reuses the finite-system subtraction theorem; `FloatingPointFormat.finiteRoundToEvenOp_add_oppositeSign_sameExponent_error_finiteSystem` records the resulting zero local error |
| All-subnormal addition exact branch | closed | `FloatingPointFormat.subnormalValue_add_sameSign_finiteSystem_of_subnormalMantissas` proves the same-sign subnormal sum stays finite representable, `FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_subnormal_eq_exact` and `FloatingPointFormat.finiteRoundToEvenOp_add_oppositeSign_subnormal_eq_exact` close same/opposite sign exactness, and `FloatingPointFormat.finiteRoundToEvenOp_add_subnormal_error_finiteSystem` records finite zero local roundoff error for arbitrary-sign all-subnormal addition |
| Mixed normal/subnormal coefficient-fits exact branch | closed | `FloatingPointFormat.normalizedValue_add_sameSign_subnormal_finiteSystem_of_alignedCoeff_lt_mantissaBound` rewrites the normalized operand onto the `emin` subnormal lattice and proves finite representability when `m * beta^(e-emin) + n < beta^t`; the two operation-order exact/error wrappers close finite zero local roundoff error for this same-sign mixed subcase |
| Mixed normal/subnormal one-guard finite-error branch | closed | `FloatingPointFormat.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_guardCoeffBounds` rewrites the normalized operand onto the `emin` lattice and feeds the aligned coefficient range `beta^t <= k < 2*beta^t` to the existing binary guard dispatcher; `FloatingPointFormat.finiteRoundToEvenOp_add_normalized_sameSign_subnormal_error_finiteSystem_of_guardCoeffBounds` and its commuted wrapper transfer this source finite-error witness to concrete finite-normal rounded addition |
| Exact-or-one-guard dispatch wrappers | closed | `FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_alignedCoeff_lt_two_mul_mantissaBound`, its commuted ordered-exponent wrapper, and the two mixed normal/subnormal `alignedCoeff < 2*beta^t` wrappers package the coefficient-fits and one-guard branches into single operation-level dependencies |
| Normalized Sterbenz opposite-sign addition exact branch | closed | `FloatingPointFormat.finiteRoundToEvenOp_add_neg_right_normalizedSystem_eq_exact_of_sterbenzRatioCondition` packages `x + (-y)` as exact Sterbenz subtraction for normalized operands, `FloatingPointFormat.finiteRoundToEvenOp_add_neg_right_normalizedSystem_error_finiteSystem_of_sterbenzRatioCondition` records the finite zero local error, and the positive normalized-value specializations expose the common `positive + negative` branch |
| Finite-system Sterbenz opposite-sign addition exact branch | closed | `FloatingPointFormat.finiteRoundToEvenOp_add_neg_right_finiteSystem_eq_exact_of_sterbenzRatioCondition` and `FloatingPointFormat.finiteRoundToEvenOp_add_neg_left_finiteSystem_eq_exact_of_sterbenzRatioCondition` package `x + (-y)` and `(-y) + x` as exact finite-system Sterbenz subtraction, including normal, subnormal, and mixed cases; their finite-error corollaries record the zero local roundoff error |
| Roundoff-error representability for a rounded binary add | open | Next Lean dependency: `finiteRoundToEvenOp_add_error_finite_of_base2_abs_order_of_finiteNormalRange`, matching the finite-normal/no-underflow/no-overflow branch of Shewchuk Corollary 2 |
| Derive the signed Sterbenz/certificate obligations from the printed base-2 hypotheses `|a| > |b|` | open | Use the acquired Shewchuk/Dekker split: exact-add branch already closed; line-2 exactness uses Sterbenz/exact-add cases; line-3 needs roundoff-error representability |
| Full all-signs base-2 FastTwoSum/TwoSum theorem for the displayed correction formula | open | Prove a theorem deriving `FastTwoSumFiniteCertificate fmt a b` from finite base-2 assumptions, then compose with `finiteCorrectionFormulaTrace_exact_of_fastTwoSumFiniteCertificate` |

## Next Proof Target

The next theorem should not be another conditional wrapper.  It should derive
one of the certificate obligations from source-level base-2 finite-format
facts.  The acquired Shewchuk/Dekker route makes the first missing dependency:

```lean
finiteRoundToEvenOp_add_error_finite_of_base2_abs_order_of_finiteNormalRange
```

This should formalize the roundoff-error representability fact used in
Shewchuk's Corollary 2: for a rounded binary addition of two finite `t`-digit
operands, the exact error `(a+b)-s` is finite representable under the source
finite-normal range assumptions.  It cannot be weakened to an arbitrary
finite-normal-range real: `FloatingPointFormat.finiteNormalRange_not_enough_for_roundoff_error_finiteSystem`
shows that the tiny binary `t = 2` format rounds the in-range real `21/16` to
`3/2` but has nonrepresentable error `-3/16`.  The next theorem therefore
needs the finite-binary-operand grid hypotheses from the actual addition.  The
first same-exponent lattice handoff is now closed by
`FloatingPointFormat.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound`;
the corresponding certificate-field handoff is now closed by
`FastTwoSumFiniteCertificate.finite_error_of_sameExponentScaledInteger`.
The aligned same-sign/same-exponent source-grid half is also closed by
`FloatingPointFormat.normalizedValue_add_sameSign_sameExponent_exists_scaledIntegerCoeff`,
which gives `a+b = sign*(m+n)*beta^(e-t)` with `m+n < 2*beta^t` for two
aligned normalized operands.  The exact aligned branch `m+n < beta^t` is closed
by
`FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_sameExponent_eq_exact_of_add_lt_mantissaBound`.
The inexact aligned branch is also closed at the source-evidence level by
`FloatingPointFormat.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_sameExponent_error_finiteSystem`.
The corresponding finite-normal operation-level wrapper is closed by
`FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_sameExponent_error_finiteSystem`.
Remaining work is to generalize the alignment split beyond this
same-sign/same-exponent case.  The pure binary
endpoint coefficient arithmetic for that comparison is closed by
`FloatingPointFormat.binaryGuardCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_ceil`;
actual source round-to-even evidence now selects exactly one of the lower or
upper same-exponent endpoint mantissas by
`FloatingPointFormat.sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between`
and
`FloatingPointFormat.sourceRoundToEvenEvidence_sameExponent_mantissa_eq_or_succ_of_bracket`.
The positive aligned guard-word quotient bracket is now constructed by
`FloatingPointFormat.binaryGuardSource_between_sameExponentEndpoints_positive`,
and the actual positive-branch evidence-to-finite-error composition is
closed by
`FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem`.
The negative same-sign branch is now closed as well by
`FloatingPointFormat.binaryGuardSource_between_sameExponentEndpoints_negative`
and
`FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem`.
The ordinary positive and negative guard-word branches also now have direct
endpoint-mantissa-free wrappers,
`FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem_of_normalizedQuotient`
and
`FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem_of_normalizedQuotient`,
which take normalized quotient endpoint hypotheses and source round-to-even
evidence directly to finite local-error representability.
The exponent-boundary guard-word branch is now closed by
`FloatingPointFormat.binaryGuardSource_between_boundaryEndpoints_positive`,
`FloatingPointFormat.binaryGuardSource_between_boundaryEndpoints_negative`, and
`FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_boundary_error_finiteSystem`
and
`FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_boundary_error_finiteSystem`.
The finite-normal source-policy handoff to the concrete add selector is now
closed by
`FloatingPointFormat.finiteRoundToEvenOp_add_error_finite_of_sourceRoundToEvenEvidence`.
The ordinary-or-boundary guard coefficient split is also now closed by
`FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem_of_guardCoeffBounds`
and
`FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem_of_guardCoeffBounds`.
The actual same-sign same-exponent normalized-operand handoff through those
wrappers is closed by
`FloatingPointFormat.sourceRoundToEvenEvidence_positive_normalizedValue_add_sameSign_sameExponent_error_finiteSystem`,
`FloatingPointFormat.sourceRoundToEvenEvidence_negative_normalizedValue_add_sameSign_sameExponent_error_finiteSystem`,
and
`FloatingPointFormat.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_sameExponent_error_finiteSystem`.
The same aligned branch is closed for the concrete finite round-to-even
operation wrapper by
`FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_sameExponent_error_finiteSystem`.
The coefficient-fits same-sign normalized ordered-exponent branch is closed by
`FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_alignedCoeff_lt_mantissaBound`
and its commuted finite-error wrapper.
The one-guard same-sign normalized ordered-exponent branch is closed by
`FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_guardCoeffBounds`
and its commuted finite-error wrapper.
The opposite-sign same-exponent exact branch is also closed by
`FloatingPointFormat.finiteRoundToEvenOp_add_oppositeSign_sameExponent_eq_exact`
and its zero-error corollary
`FloatingPointFormat.finiteRoundToEvenOp_add_oppositeSign_sameExponent_error_finiteSystem`.
The all-subnormal arbitrary-sign branch is closed by
`FloatingPointFormat.finiteRoundToEvenOp_add_subnormal_eq_exact`
and
`FloatingPointFormat.finiteRoundToEvenOp_add_subnormal_error_finiteSystem`.
The coefficient-fits same-sign mixed normal/subnormal branch is closed by
`FloatingPointFormat.finiteRoundToEvenOp_add_normalized_sameSign_subnormal_error_finiteSystem_of_alignedCoeff_lt_mantissaBound`
and
`FloatingPointFormat.finiteRoundToEvenOp_add_subnormal_sameSign_normalized_error_finiteSystem_of_alignedCoeff_lt_mantissaBound`.
The one-guard same-sign mixed normal/subnormal branch is closed by
`FloatingPointFormat.finiteRoundToEvenOp_add_normalized_sameSign_subnormal_error_finiteSystem_of_guardCoeffBounds`
and its commuted finite-error wrapper.
The exact-or-one-guard range is packaged by the ordered-exponent and mixed
normal/subnormal `alignedCoeff < 2*beta^t` wrappers, so future proofs can
dispatch that full range with a single operation-level dependency.
The normalized Sterbenz opposite-sign exact branch is closed by
`FloatingPointFormat.finiteRoundToEvenOp_add_neg_right_normalizedSystem_eq_exact_of_sterbenzRatioCondition`
and its finite-error form, with positive normalized-value specializations for
the `positive + negative` branch.
The finite-system Sterbenz opposite-sign exact branch is closed by
`FloatingPointFormat.finiteRoundToEvenOp_add_neg_right_finiteSystem_eq_exact_of_sterbenzRatioCondition`
and
`FloatingPointFormat.finiteRoundToEvenOp_add_neg_left_finiteSystem_eq_exact_of_sterbenzRatioCondition`,
with finite-error corollaries for both operand orders.  These wrappers include
subnormal and mixed finite operands once the `sterbenzRatioCondition` is
available.
The next local proof must derive the remaining normalized different-exponent
alignment cases with `alignedCoeff >= 2*beta^t`, the mixed normal/subnormal
alignment cases outside that same exact-or-one-guard range, and the remaining
opposite-sign/magnitude splits needed to feed this operation-level handoff.  The
branch-alignment lemmas
`FloatingPointFormat.finiteRoundToEven_eq_finiteNormalRoundToEven_of_finiteNormalRange`
and
`FloatingPointFormat.finiteRoundToEvenOp_eq_finiteNormalRoundToEven_of_finiteNormalRange`
now prove that the repository's total finite round-to-even wrapper agrees with
the source-style finite-normal selector on that range.  Once the error
representability lemma is closed, the full target is:

```lean
FastTwoSumFiniteCertificate.of_base2_abs_gt_of_inexact_add
```

with explicit hypotheses that `fmt.beta = 2`, `a` and `b` are finite
representable, `|b| < |a|`, the exact sum is in range, and `s ≠ a + b`,
where `s = finiteRoundToEvenOp add a b`.  Do not include a separate `s`-finite
hypothesis: `FastTwoSumFiniteCertificate.finite_s_unconditional` proves that
locally for every finite round-to-even operation.  The exact-add split is
already closed by `FastTwoSumFiniteCertificate.of_exact_add`; the next proof
should derive representability of `a-s` and `(a+b)-s` in the remaining
inexact-add cases, or narrow those obligations to the exact
Dekker/Knuth/Linnainmaa split cases.
The route that tries to obtain the first signed Sterbenz branch directly from
`|b| < |a|` is ruled out by
`correctionFormula_abs_order_not_imply_signed_sterbenz_exact_sum`.

Proof-source acquisition for this target is tracked in
`docs/CHAPTER04_PROOF_SOURCE_LEDGER.md`.
