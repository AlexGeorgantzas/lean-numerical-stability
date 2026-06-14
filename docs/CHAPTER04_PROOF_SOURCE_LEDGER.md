# Chapter 4 Proof-Source Ledger

Source: `references/Chapter04_full.pdf` and the local Higham bibliography in
`references/HighamBook.pdf`.

Status: **OPEN**.  This ledger records source chains needed for Chapter 4
claims whose proof in the excerpt is citation-only or sketch-level.  A source
record does not close a Lean theorem; a row closes only when the relevant
mathematics is proved locally or reused from a locally proved theorem.

## C4.P2 Wilkinson Recursive-Summation Attainability

Higham p. 100, Problem 4.2 cites Wilkinson 1963, p. 19 for the
powers-of-two input family showing that the recursive-summation bounds (4.3)
and (4.4) are nearly attainable.  Higham's solution sketch later explains the
intended arithmetic route: at each displayed block the low-order `2^(k-t)`
part of the term is lost in the rounded addition, so the computed sum is the
integer `2^r` while the exact source sum is smaller by the accumulated defect.

| ID | Paper claim | Missing step | Source location | Local Lean target | Status |
|---|---|---|---|---|---|
| C4.P2-S1 | Wilkinson's powers-of-two input family nearly attains recursive-summation bounds (4.3) and (4.4). | Prove the finite-format rounded trace, under the base-2 round-to-nearest/tie rule and `u = 2^-t`, that recursive summation of the displayed family returns `2^r`; then compare the resulting defect with the right-hand sides of (4.3) and (4.4). | Higham Problem 4.2, p. 100; Higham solution 4.2, p. 542; Wilkinson [1088] 1963, pp. 19--20.  Higham bibliography identifies [1088] as J. H. Wilkinson, *Rounding Errors in Algebraic Processes*, Notes on Applied Science No. 32, HMSO, London, 1963, also Prentice-Hall and Dover reprint. | The IEEE-double route is local: `wilkinsonProblem42BlockValue`, `wilkinsonProblem42Input`, `wilkinsonProblem42ExactSum`, `wilkinsonProblem42Defect`, `wilkinsonProblem42Vector`, `finiteRoundToEvenRecursiveSum`, `finiteRoundToEvenListSum`, `finiteRoundToEvenRecursiveSum_eq_listSum`, `wilkinsonProblem42BlockValue_ieeeDouble_finiteSystem`, `wilkinsonProblem42Input_ieeeDouble_all_finiteSystem`, `wilkinsonProblem42Vector_ieeeDouble_finiteSystem`, `wilkinsonProblem42_ieeeDouble_sameBinade_add_rounds_to_nat`, `wilkinsonProblem42_ieeeDouble_block_boundary_add_rounds_to_pow`, `wilkinsonProblem42_ieeeDouble_block_prefix_accumulator`, `wilkinsonProblem42_ieeeDouble_block_rounds_pow_to_next_pow`, `wilkinsonProblem42_ieeeDouble_listRecursiveSum_eq_pow`, `wilkinsonProblem42_ieeeDouble_finiteRecursiveSum_eq_pow`, `wilkinsonProblem42_ieeeDouble_abs_error_eq_defect`, `wilkinsonProblem42_ieeeDouble_abs_error_closed_form`, `wilkinsonProblem42_ieeeDouble_first_order_bound_le_four_abs_error`, and `wilkinsonProblem42_ieeeDouble_gamma_bound_le_eight_abs_error`. | Source chain identified from local `Chapter04_full.pdf` and `HighamBook.pdf`; Wilkinson theorem body remains advisory/not separately acquired.  The concrete IEEE-double instantiation is proved end to end for `t = 53`, `r <= 52`: every displayed input is finite, the arbitrary positive-length rounded trace returns `2^r`, the realized error equals the defect with the closed form, the first-order scale is within factor `4` of the realized error for positive `r`, and the exact-gamma scale is within factor `8` under the explicit denominator condition.  A fully generic arbitrary-precision `t`-digit base-2 theorem is not claimed; the resolved bottleneck and optional generic lift are tracked in `docs/CHAPTER04_P42_WILKINSON_ATTAINABILITY_BOTTLENECK.md`. |

## C4.4 Correction Formula, Equation (4.7)

Higham pp. 92--93 states that for floating-point numbers `a` and `b` with
`|a| > |b|`, if `s = fl(a+b)` and `e = fl((a-s)+b)` are evaluated in rounded
base-2 arithmetic in the displayed parenthesized order, then

```text
a + b = s + e.
```

The excerpt gives no proof and cites Dekker, Knuth, and Linnainmaa.

| ID | Paper claim | Missing step | Source location | Local Lean target | Status |
|---|---|---|---|---|---|
| C4.4-S1 | Equation (4.7), error-free correction formula in rounded base 2. | Derive representability of `a-s` and `(a+b)-s` from finite base-2 assumptions, `|b| < |a|`, and the inexact first-add split. | T. J. Dekker, "A floating-point technique for extending the available precision," *Numerische Mathematik* 18:224--242, 1971; cited by Higham as Theorem 4.7. Springer record: <https://link.springer.com/article/10.1007/BF01397083>. | `FastTwoSumFiniteCertificate.of_base2_abs_gt_of_inexact_add` should prove `FastTwoSumFiniteCertificate fmt a b` by deriving only the two genuine fields packaged by `FastTwoSumFiniteCertificate.of_error_obligations`; `s` finite is already closed by `FastTwoSumFiniteCertificate.finite_s_unconditional`. | Source record identified from Higham bibliography and Springer metadata; original theorem body not yet acquired/formalized. |
| C4.4-S2 | Same claim, alternate cited proof. | Compare Knuth's Theorem C assumptions and split cases against the local finite-format definitions. | Donald E. Knuth, *The Art of Computer Programming, Volume 2, Seminumerical Algorithms*, 2nd ed., Addison-Wesley, 1981, Theorem C, p. 221. | Same target as C4.4-S1, or a smaller split-case theorem if Knuth exposes a better dependency DAG. | Bibliographic record identified; theorem body not yet acquired/formalized. |
| C4.4-S3 | Same claim, alternate cited proof. | Compare Linnainmaa's Theorem 3 assumptions with Dekker/Knuth, especially base and rounding-mode restrictions. | Seppo Linnainmaa, "Analysis of some known methods of improving the accuracy of floating-point sums," *BIT* 14:167--202, 1974, Theorem 3. | Same target as C4.4-S1, or a smaller theorem if Linnainmaa's statement cleanly isolates the inexact-add branch. | Bibliographic record identified; theorem body not yet acquired/formalized. |
| C4.4-S4 | Same Dekker/FastTwoSum proof route, in an accessible later source. | Translate the published proof skeleton into local Lean dependencies: line-2 exactness by a two-case Sterbenz/exact-add split; line-3 exactness by representability of the addition roundoff error. | Jonathan R. Shewchuk, "Adaptive Precision Floating-Point Arithmetic and Fast Robust Geometric Predicates," CMU-CS-96-140R / *Discrete & Computational Geometry* 18(3):305--363, 1997, Section 2.3, Theorem 6; PDF <https://people.eecs.berkeley.edu/~jrs/papers/robustr.pdf>. The theorem is labeled as Dekker's FAST-TWO-SUM theorem and cites Dekker. | New local subtargets: the closed selector bridge `FloatingPointFormat.finiteRoundToEvenOp_eq_finiteNormalRoundToEven_of_finiteNormalRange`, then `finiteRoundToEvenOp_add_error_finite_of_base2_abs_order_of_finiteNormalRange` for the finite-normal/no-underflow/no-overflow Shewchuk Corollary 2 branch, then `FastTwoSumFiniteCertificate.of_base2_abs_gt_of_inexact_add` using the exact-add split plus the two Sterbenz branches. | Advisory proof body acquired; not a substitute for Lean proof. |

## C4.P9 Compensated-Summation Research Problem

Higham p. 102, Problem 4.9 cites Priest 1992, pp. 61--62 for a three-term
decreasing-absolute-value compensated-summation result and for a displayed IEEE
single-precision counterexample family.  The problem asks for the smallest `n`
for which decreasing-absolute-value compensated summation can produce a large
relative error.

| ID | Paper claim | Missing step | Source location | Local Lean target | Status |
|---|---|---|---|---|---|
| C4.P9-S1 | If `|x_1| >= |x_2| >= |x_3|`, compensated summation computes `x_1+x_2+x_3` with relative error of order `u` under reasonable arithmetic assumptions; a six-term IEEE single family can compute `0` for exact sum `2`; determine the smallest such `n`. | Acquire Priest's precise assumptions, theorem statement, and counterexample arithmetic, then translate them into local finite-format/Kahan trace hypotheses. | Priest 1992, pp. 61--62, cited directly by Higham Problem 4.9. | Candidate theorem family: a three-term ordered compensated-summation relative-error theorem over `fl_kahanSum`, an IEEE-single trace for the displayed six-term family, and a minimality theorem excluding smaller `n` under the same assumptions. | Open; source cited by Higham but not yet acquired or formalized locally. |

### Current Local Lean Evidence

- `finiteCorrectionFormulaTrace_exact_of_fastTwoSumFiniteCertificate` proves
  equation (4.7) from a finite FastTwoSum certificate.
- `FastTwoSumFiniteCertificate.finite_s_unconditional` proves that the rounded
  sum field of that certificate is automatic for the local finite real-valued
  round-to-even selector.
- `FastTwoSumFiniteCertificate.of_error_obligations` narrows the future theorem
  to representability of `a-s` and `(a+b)-s`.
- `FastTwoSumFiniteCertificate.finite_error_of_sameExponentScaledInteger`
  discharges the second field once the finite binary operand-grid proof has
  put `a+b` and `fl(a+b)` on a shared signed scaled-integer lattice with a
  `t`-digit coefficient gap.
- `FloatingPointFormat.normalizedValue_add_sameSign_sameExponent_eq_scaledInteger`,
  `FloatingPointFormat.normalizedMantissa_add_lt_two_mul_mantissaBound`, and
  `FloatingPointFormat.normalizedValue_add_sameSign_sameExponent_exists_scaledIntegerCoeff`
  close the aligned same-sign/same-exponent normalized source-grid case:
  `a+b` has coefficient `m+n` on the common exponent lattice, with
  `m+n < 2*beta^t`.
- `FloatingPointFormat.normalizedValue_add_sameSign_sameExponent_finiteSystem_of_add_lt_mantissaBound`
  and
  `FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_sameExponent_eq_exact_of_add_lt_mantissaBound`
  close the aligned exact-first-add branch when the coefficient already fits:
  `m+n < beta^t`.
- `FloatingPointFormat.binaryGuardCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_ceil`
  closes the pure binary endpoint-coefficient arithmetic for the aligned
  inexact guard-word branch: if `k = beta*q+r` and the rounded endpoint
  coefficient is the lower quotient `q` or the non-exact upper endpoint `q+1`,
  then `k-beta*l` is a `t`-digit coefficient.
- `FloatingPointFormat.binaryGuardQuotient_normalized_or_max_of_mantissaBound_le_of_lt_two_mul`
  closes the quotient-dispatch arithmetic for the aligned guard-word branch:
  a base-2 coefficient in `[beta^t, 2*beta^t)` decomposed as `k = beta*q+r`
  either supplies an ordinary normalized bracket with `q` and `q+1`, or has
  `q = maxNormalMantissa`, which selects the exponent-boundary branch.
- `FloatingPointFormat.sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between`
  and
  `FloatingPointFormat.sourceRoundToEvenEvidence_sameExponent_mantissa_eq_or_succ_of_bracket`
  close the source-policy endpoint-selection bridge for a supplied
  same-exponent adjacent bracket: actual round-to-even evidence selects the
  lower endpoint or upper endpoint, hence the normalized mantissa index is
  `q` or `q+1`.
- `FloatingPointFormat.binaryGuardSource_between_sameExponentEndpoints_positive`
  and
  `FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem`
  close the positive aligned guard-word composition: the quotient bracket is
  constructed for `k = beta*q+r`, exact remainder zero forces the lower
  endpoint, and the resulting selected endpoint gives a finite representable
  local roundoff error.
- `FloatingPointFormat.binaryGuardSource_between_sameExponentEndpoints_negative`
  and
  `FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem`
  close the negative aligned guard-word composition: the real-order quotient
  bracket is reversed, exact remainder zero still forces the quotient endpoint,
  and the selected endpoint gives the same finite representable local roundoff
  error.
- `FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem_of_normalizedQuotient`
  and
  `FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem_of_normalizedQuotient`
  remove the separate rounded-endpoint mantissa hypothesis in the ordinary
  guard-word branch: normalized quotient data for `q` and `q+1`, source
  round-to-even evidence, and the base-2 quotient split directly imply finite
  representability of the local roundoff error.
- `FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem_of_guardCoeffBounds`
  and
  `FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem_of_guardCoeffBounds`
  close the ordinary-or-boundary guard coefficient dispatch: a base-2 guard
  coefficient in `[beta^t, 2*beta^t)` now feeds either the ordinary normalized
  quotient wrappers or the max-mantissa boundary wrappers and directly returns
  finite local-error representability.
- `FloatingPointFormat.binaryGuardSource_between_boundaryEndpoints_positive`,
  `FloatingPointFormat.binaryGuardSource_between_boundaryEndpoints_negative`,
  `FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_boundary_error_finiteSystem`,
  and
  `FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_boundary_error_finiteSystem`
  close the exponent-boundary guard-word composition: when the quotient endpoint
  is `maxNormalMantissa`, the next candidate is `minNormalMantissa` at the
  following exponent, and the selected endpoint still yields a finite
  representable local roundoff error.
- `FloatingPointFormat.finiteRoundToEvenOp_add_error_finite_of_sourceRoundToEvenEvidence`
  closes the finite-normal operation-level handoff: a source round-to-even
  witness with finite local error transfers to the concrete
  `finiteRoundToEvenOp add` local error by selector uniqueness.
- `FastTwoSumFiniteCertificate.of_exact_add` and
  `finiteCorrectionFormulaTrace_exact_of_exact_add` close the exact-first-add
  split case.
- `correctionFormula_abs_order_not_imply_signed_sterbenz_exact_sum` rules out
  deriving the first signed Sterbenz branch directly from `|b| < |a|`.
- `FloatingPointFormat.finiteRoundToEven_eq_finiteNormalRoundToEven_of_finiteNormalRange`
  and
  `FloatingPointFormat.finiteRoundToEvenOp_eq_finiteNormalRoundToEven_of_finiteNormalRange`
  prove that the total finite round-to-even selector agrees with the
  source-style finite-normal selector under the no-underflow/no-overflow range
  assumptions used by the cited FastTwoSum proof route.
- `FloatingPointFormat.finiteNormalRange_not_enough_for_roundoff_error_finiteSystem`
  rules out the range-only shortcut: even in base 2, an arbitrary
  finite-normal-range real can round with a non-finite-representable exact
  error.  The missing Shewchuk/Dekker lemma must use the stronger fact that
  the rounded source value is the exact addition of finite binary operands.
- `FloatingPointFormat.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound`
  closes the first coefficient-grid bridge for the finite-operand route: once
  the exact addition source and rounded endpoint are on the same signed
  scaled-integer exponent lattice and their integer coefficient gap has fewer
  than `t` radix digits, the exact real error is finite representable.
- `FastTwoSumFiniteCertificate.finite_error_of_sameExponentScaledInteger`
  lifts that coefficient-grid bridge directly to the `finite_error` field of
  the local FastTwoSum certificate.
- `FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_alignedCoeff_lt_mantissaBound`
  and its commuted wrapper close the same-sign normalized different-exponent
  exact branch when the high exponent operand shifted to the lower exponent
  lattice plus the lower mantissa remains below `beta^t`.
- `FloatingPointFormat.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_guardCoeffBounds`
  and its operation-level wrappers close the same-sign normalized
  different-exponent one-guard branch when the aligned lower-lattice
  coefficient lies in `[beta^t, 2*beta^t)`.
- `FloatingPointFormat.finiteRoundToEvenOp_add_oppositeSign_sameExponent_error_finiteSystem`
  closes the opposite-sign same-exponent normalized add branch as exact
  same-sign same-exponent subtraction with zero local error.
- `FloatingPointFormat.finiteRoundToEvenOp_add_subnormal_error_finiteSystem`
  closes arbitrary-sign all-subnormal addition as an exact concrete
  finite-round-to-even operation, again with finite zero local error.
- `FloatingPointFormat.finiteRoundToEvenOp_add_normalized_sameSign_subnormal_error_finiteSystem_of_alignedCoeff_lt_mantissaBound`
  and
  `FloatingPointFormat.finiteRoundToEvenOp_add_subnormal_sameSign_normalized_error_finiteSystem_of_alignedCoeff_lt_mantissaBound`
  close the same-sign mixed normal/subnormal exact branch when the normalized
  coefficient shifted to the `emin` lattice plus the subnormal coefficient
  remains below `beta^t`.

### Acquired Proof Route

Shewchuk's accessible reproduction of Dekker's FAST-TWO-SUM proof gives the
local proof order.  The relevant source dependencies are:

1. A roundoff-error representability lemma: the error in a rounded addition of
   two `p`-bit binary floating-point values is itself expressible with `p`
   bits in the finite-normal/no-underflow/no-overflow source branch.  This is
   Shewchuk's Corollary 2 and is not yet local.  The local counterexample
   `FloatingPointFormat.finiteNormalRange_not_enough_for_roundoff_error_finiteSystem`
   shows why the Lean target must include finite binary operand hypotheses,
   not only a finite-normal-range hypothesis on the exact source real.  The
   local theorem
   `FloatingPointFormat.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound`
   supplies the same-exponent coefficient-grid handoff once the addition
   proof has produced the shared lattice exponent and coefficient-gap bound;
   `FastTwoSumFiniteCertificate.finite_error_of_sameExponentScaledInteger`
   then turns it into the certificate's `finite_error` obligation.
   The aligned same-sign/same-exponent source grid is now closed by
   `FloatingPointFormat.normalizedValue_add_sameSign_sameExponent_exists_scaledIntegerCoeff`;
   if that coefficient satisfies `m+n < beta^t`, then
   `FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_sameExponent_eq_exact_of_add_lt_mantissaBound`
   closes the exact-add branch.  The remaining aligned branch work is the
   inexact guard-word case `beta^t <= m+n < 2*beta^t`: compare the resulting
   source coefficient with the adjacent rounded endpoint.  The pure binary
   lower/upper endpoint coefficient-gap arithmetic is now closed by
   `FloatingPointFormat.binaryGuardCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_ceil`;
   actual source round-to-even endpoint selection is now closed by
   `FloatingPointFormat.sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between`
   and
   `FloatingPointFormat.sourceRoundToEvenEvidence_sameExponent_mantissa_eq_or_succ_of_bracket`.
   The positive aligned guard-word bracket and finite-error composition are
   now closed by
   `FloatingPointFormat.binaryGuardSource_between_sameExponentEndpoints_positive`
   and
   `FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem`;
   the endpoint-mantissa-free wrapper
   `FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem_of_normalizedQuotient`
   now composes the bracket and coefficient-gap proof directly from normalized
   quotient endpoint hypotheses.
   The negative same-sign branch is now closed by
   `FloatingPointFormat.binaryGuardSource_between_sameExponentEndpoints_negative`
   and
   `FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem`;
   the endpoint-mantissa-free wrapper
   `FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem_of_normalizedQuotient`
   gives the corresponding direct composition for the reversed real-order
   bracket.
   The exponent-boundary guard-word branch is now closed by the
   `FloatingPointFormat.binaryGuardSource_between_boundaryEndpoints_positive`,
   `FloatingPointFormat.binaryGuardSource_between_boundaryEndpoints_negative`,
   `FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_boundary_error_finiteSystem`,
   and
   `FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_boundary_error_finiteSystem`.
   The ordinary-or-boundary guard coefficient dispatcher is now closed by
   `FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem_of_guardCoeffBounds`
   and
   `FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem_of_guardCoeffBounds`.
   The finite-normal operation-level handoff is closed by
   `FloatingPointFormat.finiteRoundToEvenOp_add_error_finite_of_sourceRoundToEvenEvidence`.
   The same-sign normalized ordered-exponent coefficient-fits exact branch is
   closed by
   `FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_alignedCoeff_lt_mantissaBound`
   and its commuted wrapper.
   The same-sign normalized ordered-exponent one-guard branch is closed by
   `FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_guardCoeffBounds`
   and its commuted wrapper.
   The opposite-sign same-exponent normalized branch is closed by
   `FloatingPointFormat.finiteRoundToEvenOp_add_oppositeSign_sameExponent_error_finiteSystem`,
   and the all-subnormal arbitrary-sign branch is closed by
   `FloatingPointFormat.finiteRoundToEvenOp_add_subnormal_error_finiteSystem`.
   The same-sign mixed normal/subnormal coefficient-fits exact branch is
   closed by the two mixed operand-order finite-error wrappers.  The same-sign
   mixed normal/subnormal one-guard branch is closed by
   `FloatingPointFormat.finiteRoundToEvenOp_add_normalized_sameSign_subnormal_error_finiteSystem_of_guardCoeffBounds`
   and its commuted wrapper.  The ordered-exponent and mixed normal/subnormal
   exact-or-one-guard dispatch wrappers now package the full
   `alignedCoeff < 2*beta^t` range as a single operation-level dependency.  The
   next proof step is to derive the remaining normalized different-exponent
   alignment cases with `alignedCoeff >= 2*beta^t`, the mixed alignment cases
   outside that range, and the unresolved opposite-sign/magnitude splits needed
   to feed that handoff.
2. A line-2 exactness split for `s - a`: one branch uses Sterbenz directly;
   the opposite-sign large-cancellation branch first proves the initial add is
   exact.  The exact-add branch is already closed locally by
   `FastTwoSumFiniteCertificate.of_exact_add`.
3. A line-3 exactness step for `b - (s-a)`, using the roundoff-error
   representability lemma.  In the local certificate formulation this is the
   remaining `finite_error` field.

### Next Source Acquisition Step

Acquire at least one original theorem body among Dekker Theorem 4.7, Knuth
Theorem C, or Linnainmaa Theorem 3 if available.  In parallel, the next Lean
proof target from the acquired Shewchuk route is the roundoff-error
representability lemma
`finiteRoundToEvenOp_add_error_finite_of_base2_abs_order_of_finiteNormalRange`,
with explicit finite binary operands, because it is the unformalized source
dependency needed to close line 3 of FAST-TWO-SUM in the ordinary
finite-normal arithmetic branch.  A version stated only for arbitrary in-range
reals is now ruled out by local Lean evidence; the next local subtarget is to
derive the shared lattice exponent and `t`-digit coefficient gap needed by
`FloatingPointFormat.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound`
and `FastTwoSumFiniteCertificate.finite_error_of_sameExponentScaledInteger`
from two finite binary operands and the adjacent rounded endpoint.
For the aligned same-sign/same-exponent normalized branch, the source-grid
representation of `a+b` and the exact `m+n < beta^t` operation branch are
already local.  The endpoint coefficient arithmetic for the remaining
`beta^t <= m+n < 2*beta^t` guard word is also local, and the actual
round-to-even evidence bridge now identifies the selected same-exponent
mantissa as the quotient endpoint `q` or the non-exact successor endpoint
`q+1` once the adjacent bracket is supplied.  The positive and negative
same-sign branches now build the concrete quotient brackets and compose them
through the coefficient-gap obligation into finite local-error representability,
and the max-mantissa exponent-boundary guard-word branch now returns the
corresponding next-binade endpoint coefficient and finite local-error
representability.  The same-sign normalized ordered-exponent coefficient-fits
branch, the same-sign normalized ordered-exponent one-guard branch, the
opposite-sign same-exponent normalized branch, the all-subnormal arbitrary-sign
branch, the same-sign mixed normal/subnormal coefficient-fits branch, and the
same-sign mixed normal/subnormal one-guard branch are also closed.  The
exact-or-one-guard dispatch wrappers close the ordered-exponent and mixed
`alignedCoeff < 2*beta^t` range as a reusable operation-level dependency.  The
next subtarget is the remaining normalized different-exponent alignment with
`alignedCoeff >= 2*beta^t`, the mixed alignment cases outside that range, and
the unresolved opposite-sign/magnitude splits.
