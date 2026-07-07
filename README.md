# LeanFpAnalysis

A Lean 4 library for formally verified floating-point error analysis, following Higham's *Accuracy and Stability of Numerical Algorithms* (2nd ed., SIAM, 2002).

The core results are machine-checked with **zero sorry statements**. Proofs use tight constants matching Higham exactly where the library proves the full local analysis (e.g., γ(n) not γ(n+1) for the dot product bound). Some high-level chapter modules intentionally expose abstract interfaces whose hypotheses state the remaining local algorithm analysis explicitly.

## Floating-point model

The library uses an axiomatic floating-point model ([`FP/Model.lean`](LeanFpAnalysis/FP/Model.lean)) rather than a concrete IEEE 754 representation. Every arithmetic operation satisfies:

```
fl(x ∘ y) = (x ∘ y)(1 + δ),  |δ| ≤ u
```

where `u` is the unit roundoff. This makes all results valid for **any** floating-point system satisfying the standard model.

## Exact algebra and matrix norms

Exact algebra and norm infrastructure uses Mathlib as the source of truth. For
Mathlib-native matrices, theorem statements should use Mathlib notation directly,
for example `‖A‖` under the appropriate matrix norm scope.

The current algorithm layer still contains legacy function-shaped matrices
`Fin m → Fin n → ℝ`. For those APIs, the library provides documented
compatibility wrappers such as `frobNorm` and `infNorm`. These wrappers are not
independent norm definitions; they coerce through `Matrix.of` and then use
Mathlib's matrix norms. New exact matrix-facing APIs should prefer the
rectangular alias `RMat m n := Matrix (Fin m) (Fin n) ℝ` when possible, while
existing `fl_*` algorithms may continue to use `RMatFn m n := Fin m → Fin n → ℝ`
during gradual migration.

## What's covered

The library formalizes reusable results and stability contracts from **Chapter 1**, selected **Chapter 2** model algebra, core **Chapters 3-6** results, **Chapters 8 and 9** of Higham, plus selected higher-chapter interfaces used for compositional stability proofs. It also includes a RandNLA case study for the explicit meta-algorithms in Drineas and Mahoney's CACM survey, ["RandNLA: Randomized Numerical Linear Algebra"](https://dl.acm.org/doi/10.1145/2842602).

Chapter 16 Sylvester-equation work is tracked in
[`docs/source_coverage/higham_ch16.md`](docs/source_coverage/higham_ch16.md).
The current Split 3B surface includes the rectangular Sylvester equation,
vec/Kronecker wrappers, diagonal-coefficient and supplied-Schur foundations,
Lyapunov specialization, nonnegative sep-infimum/lower-bound bridge
infrastructure, a posteriori residual bounds, generalized/Riccati residual
predicates, and the SVD-coordinate
backward-error amplification vocabulary. The latter now names Higham's
Chapter 16.2 amplification factor `sylvesterAmplificationMu`, its square-case
specialization `sylvesterAmplificationMuSquare`, and the source formula bridge
`sylvesterAmplificationMu_square_eq`, the conditional square-case
`one_le_sylvesterAmplificationMuSquare`, plus the xi-level μ-relative-residual
bound `xiSq_le_mu_relative_residual_sq`. It also constructs the coordinatewise
SVD optimizer through `svdOptimalDeltaA`, `svdOptimalDeltaB`,
`svdOptimalDeltaC`, `svdOptimalPerturbations_cost_eq_xiSq`, and
`exists_svdOptimalPerturbations`, plus the component bounds
`svdOptimalPerturbations_frobNormSq_bounds`, and lifts that optimizer to an
original-coordinate backward-error certificate via
`isBackwardError_sqrt_xiSq_of_svdOptimalPerturbations`. It now models eta as the
infimum `sylvesterBackwardErrorInf` over nonnegative backward-error certificates
and proves the two-sided xi bridge with
`sylvesterBackwardErrorInf_le_sqrt_xiSq_of_svdOptimalPerturbations` and
`sqrt_xiSq_div_three_le_sylvesterBackwardErrorInf_of_svd`, and closes the direct
eta-residual amplification wrapper
`sylvesterBackwardErrorInf_le_mu_relative_residual_of_svd`, while leaving an
attained-minimum theorem open.
It also connects square Frobenius
backward-error certificates to the SVD-coordinate lower-direction bridge through
`sylvesterBackwardResidual`, `svdResidual_backwardResidual`, and
`xiSq_le_three_eta_sq_of_backward_error`. The Lyapunov subsection now also has
the spectral-coordinate equation surface `lyapunovBackwardScalarEq` and its
residual/diagonal bridges `lyapunovBackwardScalarEq_iff_residual_eq` and
`lyapunovBackwardScalarEq_iff_diagMatrix_eq`, plus the `lyapunovXiSq`,
`lyapunovAmplificationMu`, and `lyapunovXiSq_le_mu_relative_residual_sq`
surfaces. It also bridges the original-coordinate perturbation residual
`lyapunovBackwardResidual` to the diagonal spectral residual via
`lyapunovSpectralTransform_backwardResidual` and
`lyapunovBackwardScalarEq_of_spectral_decomposition`; the full eta amplification
theorem and several condition/practical-bound rows remain open in the Chapter 16
ledger.
The perturbation section also has a certificate-based (16.23)-(16.24) bridge:
`sylvesterScaledPerturbationTripleNorm`,
`sylvesterScaledPerturbationTripleNorm_le_sqrt_three_mul`,
`SylvesterPsiFirstOrderBound`, and
`sylvester_relative_first_order_bound_of_psi` prove the printed
`sqrt 3 * Psi * epsilon` first-order relative bound from a structured Psi
certificate, while leaving the exact displayed `P^{-1}` operator-norm
realization open.

Chapter 17 stationary-iteration work is tracked in
[`docs/source_coverage/higham_ch17.md`](docs/source_coverage/higham_ch17.md).
The existing `StationaryIteration.lean` module now carries the correct
2nd-edition Chapter 17 source labels and exposes a source-sign wrapper
`SourceComputedIteration` for equation (17.1), plus a bridge
`computedIteration_of_sourceComputedIteration` and source-sign one-step error
recurrence `one_step_error_source`. The current proved surface covers
nonsingular splitting algebra, the exact-solution affine fixed-point identity
`stationary_solution_fixed_point` behind (17.4), the exact finite-sum solution
identity `stationary_solution_finite_sum`, the source-sign computed finite-sum
identity `sourceComputedIteration_finite_sum` for (17.3), and the finite-sum
error recurrence `sourceComputedIteration_error_finite_sum` for (17.5), the
finite-sum residual recurrence `residual_finite_sum` for (17.18), the
finite sigma-form residual estimate `normwise_residual_sigma_finite_bound` for
(17.19), and the finite source-sigma diagonalization certificate
`finiteResidualSigma_le_diagonalizable_bound`, the entrywise `tsum` sigma
surface `residualSigmaTsumMatrix` and scalar wrapper `residualSigmaTsum`, now
instantiated with the displayed finite maximum by `diagonalResidualRatioMax`
and `finiteResidualSigma_le_diagonalizable_max_bound`, the direct literal
`tsum` bound `residualSigmaTsum_le_diagonalizable_max_bound_direct`, the
series bridge `residualSigmaTsum_le_diagonalizable_max_bound`, plus the
supremum-envelope wrapper `residualSigmaSup_le_diagonalizable_max_bound`, for
the (17.20) bound,
the singular exact-iterate identity `singular_stationary_iterate_finite_sum`
for (17.21), the consistent-system singular telescoping wrappers
`singular_consistent_source_term_eq_I_sub_G`,
`singular_consistent_second_term_telescope`, and
`singular_stationary_iterate_consistent_split` toward (17.26), plus
`singularErrorSourceTerm` for the (17.28) `S_m` source term and
`singular_error_split_finite` for the finite algebraic core of the (17.27)
range/null source split, now with the Drazin-projector wrapper
`singular_error_split_finite_of_indexOneDrazin_projector` discharging the
fixed-null component hypothesis from an index-one Drazin certificate for
`I - G`, plus the complementary projector algebra
`stationaryDrazinFixedProjector_idempotent`,
`stationaryDrazinRangeProjector_mul_fixedProjector_eq_zero`,
`stationaryDrazinFixedProjector_mul_rangeProjector_eq_zero`, and
`stationaryDrazinFixedProjector_matPow_fixed` needed on the path to the
semiconvergent limit projector.  The range side now also has
`stationaryDrazinRangeProjector_commutes_with_G`,
`stationaryDrazinRangeProjector_commutes_with_matPow`, and
`stationaryDrazinRangeProjector_matPow_sandwich`, supporting the future
range-series manipulation in (17.30).
The scale-independence passage on p.327 now has checked algebraic and
characteristic-polynomial wrappers through `stationaryRowColumnScale`,
`stationaryScaledInverse`, `stationaryRowColumnScale_splittingSpec`,
`stationaryScaledIterMatrix_similarity`, and
`stationaryScaledIterMatrix_charpoly_eq`, proving that corresponding diagonal
row/column scaling preserves the splitting, makes the scaled iteration matrix
diagonally similar to the original one, and preserves its characteristic
polynomial.
It also adds the finite (17.29) `S_m` bound surfaces
`singularErrorSourceNormSum`, `singularErrorSourceComponentBound`,
`singularErrorSourceTerm_norm_bound`,
`local_error_normwise_simplified`,
`singularErrorSourceTerm_norm_bound_of_local_error`,
`singularErrorSourceTerm_componentwise_bound`, and
`singularErrorSourceTerm_componentwise_bound_of_local_error`, with both the
normwise and componentwise forms instantiated from the local-error model and
iterate-growth hypotheses.
The module also contains the
subordinate-norm stopping-test wrappers
`stopping_test_rhs_backward_subordinate`,
`stopping_test_matrix_backward_subordinate`, and
`stopping_test_mixed_backward_subordinate` for (17.33a)-(17.33c), plus the
componentwise absolute-value stopping-test wrappers
`stopping_test_rhs_backward_componentwise`,
`stopping_test_matrix_backward_componentwise`, and
`stopping_test_mixed_backward_componentwise` from the Theorem 7.3/Oettli-Prager
route described after (17.33).  It also
models the iterate-growth constants from (17.7) and (17.9)
with `normwiseIterateGrowth`, `componentwiseIterateGrowth`, and their bound
wrappers, and adds the finite/certificate correction and infinity-norm bridge
for (17.13)-(17.15) through `finiteForwardCorrection`,
`mainForwardBoundVector`, `finiteForwardCorrection_norm_bound`, and
`finite_norm_form_forward_bound`.  The Jacobi specialization now also has the
finite norm-form surface `jacobiForwardBoundVector`,
`mainForwardBoundVector_eq_jacobiForwardBoundVector`, and
`finite_norm_form_jacobi_forward_bound`; the SOR specialization now adds
`sorForwardFactor`, `mainForwardBoundVector_norm_le_sorForwardBoundVector`, and
`finite_norm_form_sor_forward_bound`, with the Gauss-Seidel `omega = 1`
corollary `sorForwardFactor_one` and
`finite_norm_form_gaussSeidel_forward_bound`.  The exact infinite-sum,
literal infinite-sigma, and singular-system Drazin/semiconvergence rows needed
to derive Drazin existence, identify the limit of `G^m`, and close the limiting
singular forward-error formulas remain open in the Chapter 17 ledger.

Chapter 19 QR work is tracked in
[`docs/source_coverage/higham_ch19.md`](docs/source_coverage/higham_ch19.md).
The current Split 3B route has checked source-faithful Householder
normalization certificate surfaces, including a named stronger normalization
model boundary, exact one-tail and first-two certificate constructors, and an
exact-arithmetic all-stage tail-vector bridge that feeds the Theorem 19.13
final-panel pipeline through those certificates. The all-stage tail-vector
premise now also has explicit zero, one-column, and two-step constructors for
both the exact-unit-roundoff and arbitrary-model package surfaces, so future
stored-loop induction work can assemble the package without unfolding the
recursive definition. The stronger-model boundary now also exposes
sufficient-condition constructors from agreement with the
exact Higham normalized vector and from exact computed Householder vector/beta
agreement, plus an exact add/mul/div/sqrt operation route, the exact-arithmetic
normalized-vector equality, and raw, record, full-stage, source-closure,
final-closed, and final-panel endpoint wrappers from all-stage tail-vector
equalities. The recursive source-faithful certificate package is now also
proved equivalent to both the expanded raw tail-normalized package and the
named tail-normalized record package, so later stored-loop work can target any
of those surfaces while still proving the same vector-equality and self-dot
fields. The exact primitive-operation route is now also threaded directly
through the raw, record, source-closure, final-closed, and final-panel endpoint
wrappers, and exact subtraction now discharges the remaining subtract-zero copy
premise on the exact primitive-operation final-closed/final-panel variants and
on the source-closure, tail-normalized, source-faithful,
normalization-model, and full-stage final-closure endpoints, with matching
source-closure, tail-normalized, source-faithful, normalization-model, and
full-stage final-panel wrappers now available. One-entry route audits now also
prove that the stronger normalization-model predicate is not a consequence of
arbitrary `FPModel`, and that literal equality to `fl_householderNormalizedVector`
still does not imply the full source-faithful normalization certificate without
the self-dot field. The unnormalized route now also has
pivot-zero signed-active-vector bridges identifying the stored signed vector
with the exact or computed unnormalized Householder vector, plus a betaSpec
normalization bridge showing that, under nonzero-column and exact primitive
operation hypotheses, betaSpec-normalizing that unnormalized vector gives the
computed normalized Householder vector. The normalized signed-active vector is
now also packaged as a source-faithful normalization certificate under the same
computed-alpha or exact-alpha exact primitive-operation hypotheses; this
certifies the normalized vector produced from the signed active vector and
`householderBetaSpec`, not the raw unnormalized stored vector. The same
certificate route now has leading-block variants that discharge the nonzero
active-column premise from first leading-block determinant nonbreakdown, so
callers can use the standard stored-loop nonbreakdown surface instead of
supplying a separate nonzero-column fact. The same certificate surface now has
tail-leading-block variants for successor panels, deriving the once-shrunk
panel's nonzero source-column premise from determinant nonbreakdown of
`qrLeadingBlock (trailingPanel A)` under the same exact primitive-operation and
computed-alpha/exact-alpha hypotheses. That bridge is now threaded through the
first-pivot signed stored-panel handoff under the same exact-operation and
update-compatibility surfaces, so the first QR storage step can consume the
computed normalized vector while the stored route keeps the signed active vector
and `householderBetaSpec`. The same route now reaches the pivot-1 successor
step: the full stored loop keeps the zero-prefixed signed active vector and
`householderBetaSpec`, while the once-shrunk trailing panel uses the computed
normalized reflector with beta `1`, and exact subtraction now discharges its
subtract-zero copy premise. That successor handoff is now threaded through the
arbitrary-width two-step QR recursion, so the second stored active
`householderBetaSpec` step can feed the twice-shrunk trailing QR panel under the
same exact-operation and update-compatibility/exact-add-mul surfaces. Exact-alpha
variants expose the same bridge when the successor alpha is stated as Higham's
exact `householderAlpha` rather than the computed `fl_householderAlpha`. Exact
subtraction also discharges the subtract-zero copy premise for those
computed-alpha and exact-alpha successor QR recursion wrappers. The lower
successor stored-panel handoff now has matching tail-leading-block variants
that derive the nonzero trailing source-column premise from determinant
nonbreakdown of the once-shrunk trailing leading block. The tail-leading-block
successor QR variants also derive the same premise from the successor
leading-block determinant, so callers can use the determinant nonbreakdown
surface instead of supplying that column fact separately. The
full rounded stored-loop proof remains open until the per-stage certificate
fields are proved from a source-faithful model or replaced by a separate
compatibility/perturbation theorem.

For a searchable map from stability-analysis goals to files, definitions, and
theorem names, see [`docs/LIBRARY_LOOKUP.md`](docs/LIBRARY_LOOKUP.md).  For a
Lean `#check` companion index, see [`examples/LibraryLookup.lean`](examples/LibraryLookup.lean).
Recent verification for the current synchronized head includes the focused
Chapter 19 check, rebuilt Chapter 9/10 and matrix-powers merge dependencies, and
the full `examples/LibraryLookup.lean` smoke check. Representative Slot 1 checks
for Chapters 1-6 pass.
Chapter 1-6 audit summary: Chapter 1 empirical-output rows remain
experiment/model artifacts; Chapter 2 finite-format, IEEE, and guard-digit
selector work is current; Chapter 3 covers Problems 3.1--3.12 with historical
platform rows treated as empirical output; Chapter 4 records no selected
blocker, with Problem 4.10 retained as research/experiment scope; Chapter 5
covers polynomial evaluation and derivative Horner surfaces; Chapter 6 covers
norm interpolation, SVD, perturbation, and condition-number surfaces.

### Core theory

Empirical-output scope note: archived reverse inverse-square printed-value
rows are retained as optional repository-model lookup material only.  The
historical Fortran reverse `10^9` printout is closed in the Chapter 1 ledger as
`empirical-source-output` and represented by
`experiments/chapter01/reverse_inverse_square.c`; those archived optional
lemmas must not be selected as active Chapter 1 gate obligations unless a fully
specified machine/routine/display model is supplied.

| Topic | Source | Key results |
|---|---|---|
| Chapter 2 finite-format vocabulary and model surfaces | Higham §2.1--§2.2, Lemma 2.1, Theorem 2.3, equations (2.1), (2.4)--(2.5) | `FloatingPointFormat`, `FloatingPointFormat.ieeeSingleFormat`, `FloatingPointFormat.ieeeSingleFormat_unitRoundoff`, `FloatingPointFormat.ieeeDoubleFormat`, `FloatingPointFormat.ieeeDoubleFormat_unitRoundoff`, `FloatingPointFormat.normalizedMantissa`, `FloatingPointFormat.subnormalMantissa`, `FloatingPointFormat.normalizedValue`, `FloatingPointFormat.finiteSystem`, `FloatingPointFormat.digitStringInRange`, `FloatingPointFormat.positionalMantissa`, `FloatingPointFormat.positionalValue`, `FloatingPointFormat.nearestRoundingToUnbounded`, `FloatingPointFormat.realOrderAdjacentNormalized`, `FloatingPointFormat.normalizedValue_abs_between_beta_powers`, `FloatingPointFormat.normalizedValue_minNormalMantissa_abs_eq`, `FloatingPointFormat.normalizedValue_maxNormalMantissa_abs_eq`, `FloatingPointFormat.normalizedSystem_abs_bounds`, `FloatingPointFormat.normalizedValue_eq_iff_sign_exp_mantissa`, `FloatingPointFormat.positionalMantissa_normalized`, `FloatingPointFormat.exists_normalizedDigitString_positionalMantissa_eq`, `FloatingPointFormat.digitStringInRange_eq_of_positionalMantissa_eq`, `FloatingPointFormat.subnormalValue_abs_lt_min_normal`, `FloatingPointFormat.subnormalValue_succ_spacing`, `FloatingPointFormat.subnormalValue_boundary_spacing`, `FloatingPointFormat.normalizedValue_sameExponent_no_between_succ`, `FloatingPointFormat.normalizedValue_sameSign_no_between_succ`, `FloatingPointFormat.normalizedValue_no_between_succ`, `FloatingPointFormat.normalizedValue_boundary_no_between`, `FloatingPointFormat.normalizedValue_false_lt_of_exp_lt`, `FloatingPointFormat.normalizedValue_true_lt_of_exp_lt`, `FloatingPointFormat.sameExponentAdjacentNormalized_no_between`, `FloatingPointFormat.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized`, `FloatingPointFormat.boundaryAdjacentNormalized_no_between`, `FloatingPointFormat.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized`, `FloatingPointFormat.adjacentNormalized_no_between`, `FloatingPointFormat.realOrderAdjacentNormalized_of_adjacentNormalized`, `FloatingPointFormat.realOrderAdjacentNormalized_same_sign_of_representations`, `FloatingPointFormat.realOrderAdjacentNormalized_false_ordered_exp_eq_or_succ`, `FloatingPointFormat.realOrderAdjacentNormalized_false_ordered_same_exp_mantissa_succ`, `FloatingPointFormat.realOrderAdjacentNormalized_false_ordered_adjacentNormalized`, `FloatingPointFormat.realOrderAdjacentNormalized_false_representations_adjacentNormalized`, `FloatingPointFormat.adjacentNormalized_of_realOrderAdjacentNormalized`, `FloatingPointFormat.realOrderAdjacentNormalized_spacing_bounds_left`, `FloatingPointFormat.nat_floor_exact_or_successor_bracket`, `FloatingPointFormat.exists_unboundedNormalized_or_realOrderAdjacent_bracket_sameExponent`, `FloatingPointFormat.exists_unboundedNormalized_or_realOrderAdjacent_bracket_sameExponent_negative`, `FloatingPointFormat.nearestRoundingToUnbounded_exact_signedRelErrorWitness`, `FloatingPointFormat.nearestRoundingToUnbounded_eq_left_or_right_of_realOrderAdjacent_between`, `FloatingPointFormat.exists_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between`, `FloatingPointFormat.nearestAdjacentRoundAway_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between`, `FloatingPointFormat.nearestAdjacentRoundAway_signedRelErrorWitness_lt_of_nonneg_between`, `FloatingPointFormat.nearestAdjacentRoundAway_signedRelErrorWitness_lt_of_nonpos_between`, `FloatingPointFormat.nearestRoundingToUnbounded_abs_sub_le_unitRoundoff_mul_self_of_nonneg_between`, `FloatingPointFormat.nearestRoundingToUnbounded_abs_sub_le_unitRoundoff_mul_self_of_nonpos_between`, `FloatingPointFormat.nearestRoundingToUnbounded_signedRelErrorWitness_of_nonneg_between`, `FloatingPointFormat.nearestRoundingToUnbounded_signedRelErrorWitness_of_nonpos_between`, `FloatingPointFormat.exists_nearestRoundingToUnbounded_signedRelErrorWitness_of_nonneg_between`, `FloatingPointFormat.exists_nearestRoundingToUnbounded_signedRelErrorWitness_of_nonpos_between`, `FloatingPointFormat.exists_nearestRoundingToUnbounded_signedRelErrorWitness_sameExponent_positive`, `FloatingPointFormat.exists_nearestRoundingToUnbounded_signedRelErrorWitness_sameExponent_negative`, `FloatingPointFormat.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_sameExponent_positive`, `FloatingPointFormat.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_sameExponent_negative`, `FloatingPointFormat.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_sameExponent_positive`, `FloatingPointFormat.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_sameExponent_negative`, `FloatingPointFormat.finiteUnderflowRoundToEven`, `FloatingPointFormat.finiteRoundToEven`, `FloatingPointFormat.finiteRoundToEven_nearestRoundingToFinite`, `FloatingPointFormat.finiteRoundToEven_inverseRelErrorWitness_of_finiteNormalRange`, `FloatingPointFormat.normalizedValue_succ_spacing`, `FloatingPointFormat.normalizedValue_boundary_spacing`, `FloatingPointFormat.adjacentNormalized_abs_sub`, `FloatingPointFormat.adjacentNormalized_endpoint_data`, `FloatingPointFormat.adjacentNormalized_spacing_bounds_left`, `FloatingPointFormat.adjacentNormalized_realOrder_spacing_bounds_left`, `FloatingPointFormat.unitRoundoff_eq_half_machineEpsilon`, `FPModel.model_basicOp`, `FPModel.model_sqrt`, `inverseRelErrorWitness`, `inverseRelErrorModel`, `inverseRelErrorModel_iff_relErrorComputedDenom_le`, `inverseRelErrorModel_abs_exact_sub_computed_le` |
| Error measures, precision/accuracy vocabulary, and Chapter 1 sources | Higham §1.1–1.4, Problem 1.1 | `BasicOp`, `FPModel.model_basicOp`, `absError`, `relError`, `relErrorComputedDenom`, `problem_1_1_relError_bounds`, `relError_smul`, `signedRelErrorWitness`, `normwiseRelError`, `compRelError`, `compRelErrorBounded`, `ErrorSource`, `AccuracyMeasure`, `PrecisionMeasure`, `BasicOperationPrecisionBounded`, `FPModel.basicOperationPrecisionBounded`, `fl_mul_accuracy_witness_of_precision`, `fl_mul_relError_le_precision`, `SimulatesHigherPrecision` |
| Near-integer table ambiguity | Higham Problem 1.2 | `problem12TableConsistent`, `problem_1_2_candidateBelow_consistent`, `problem_1_2_candidateInteger_consistent`, `problem_1_2_table_does_not_force_last_digit_four` |
| Chapter 1 stability, cancellation, complex square roots, and residuals | Higham §1.5–1.10, Problems 1.3--1.4 | `backwardErrorBounded`, `forwardErrorBounded`, `normwiseBackwardErrorBoundedVec`, `normwiseConditionNumberBoundedVec`, `normwise_forward_from_backward_vec`, `mixedForwardBackwardErrorBounded`, `isNumericallyStable`, `isForwardStableRelativeTo`, `condNumber`, `forward_from_backward`, `relError_subtract_perturbed_le_eps_amp`, `one_sub_cos_eq_two_sin_sq_half`, `trigCancellationExactScaled_le_half`, `trigCancellationDirectScaledFromCos_abs_error_le`, `trigCancellationRewriteScaledFromSinHalf_abs_error_le_direct_cos_bound`, `problem_1_3_sqrt_one_add_sub_one`, `problem_1_3_lawOfCosines_sqrt_halfAngle`, `complexSqrtStable_nonnegA_sq`, `complexSqrtStable_negA_sq`, `complexSqrtStable_zero_sq`, `trigCancellationDirectScaled_eq`, `trigCancellationRewriteScaled_eq_half`, `roundedExactSolution_residual_norm_le_opNorm2_mul_relative_error`, `roundedExactSolution_relativeResidual2_le_relative_error_factor`, `higham_lemma_1_1_relativeResidual2_predicate`, `relativeResidual2_le_of_relativeMatrixOnlyBackwardError2Le` |
| Calculator upside-down words | Higham Problem 1.6 | `CalculatorGlyph`, `calculatorInvertDigits`, `problem_1_6_07734_hello`, `problem_1_6_5773857734_hells_bells`, `problem_1_6_real_sqrt_31438449_eq_5607` |
| Quadratic equation exact algebra, rounded discriminant, root clustering, branch rounding, computed/supplied-sqrt perturbation, recovery step, sign-of-`b` rounded pair, and scaling examples | Higham §1.8 | `quadraticRootPlus_is_root`, `quadraticRootMinus_is_root`, `quadratic_roots_product`, `quadraticRootMinus_eq_c_div_a_mul_rootPlus`, `quadraticRootSmallByBSign_abs_le_largeByBSign`, `quadraticRootPlus_sub_midpoint_abs_eq`, `quadraticRootMinus_sub_midpoint_abs_eq`, `quadraticRootSeparation_abs_eq`, `quadraticRoots_near_midpoint_of_discriminant_le`, `quadraticRoots_near_midpoint_of_discriminant_guard_failure`, `quadraticRootPlusNumerator_abs_le_of_b_nonneg_s_close`, `quadraticRootMinusNumerator_abs_le_of_b_nonpos_s_close`, `flQuadraticDiscriminant_expansion`, `flQuadraticDiscriminant_abs_error_le`, `flQuadraticDiscriminant_nonneg_of_abs_error_bound_le`, `flQuadraticRootPlusFromSqrt_rel_error_le_gamma3`, `flQuadraticRootMinusFromSqrt_rel_error_le_gamma3`, `quadraticRootPlus_sqrt_perturb_abs_le_of_abs_eps_le`, `quadraticRootMinus_sqrt_perturb_abs_le_of_abs_eps_le`, `quadraticRootPlus_sqrt_abs_perturb_abs_le_of_abs_sub_le`, `quadraticRootMinus_sqrt_abs_perturb_abs_le_of_abs_sub_le`, `flQuadraticRootPlusWithSqrtRelError_abs_error_le`, `flQuadraticRootMinusWithSqrtRelError_abs_error_le`, `flQuadraticRootPlusFromSqrt_abs_input_error_le`, `flQuadraticRootMinusFromSqrt_abs_input_error_le`, `quadraticSqrt_abs_error_le_of_discriminant_abs_error`, `flQuadraticRootPlusFromSqrt_discriminant_abs_error_le`, `flQuadraticRootMinusFromSqrt_discriminant_abs_error_le`, `flQuadraticRootPlusRoundedDiscriminantSqrt_abs_error_le`, `flQuadraticRootMinusRoundedDiscriminantSqrt_abs_error_le`, `flQuadraticRootPlusComputedSqrt_abs_error_le`, `flQuadraticRootMinusComputedSqrt_abs_error_le`, `flQuadraticRecoveredRootFromOther_rel_error_le_gamma2`, `flQuadraticRecoveredRootMinusFromRoundedPlusDiscriminantSqrt_abs_error_le`, `flQuadraticRecoveredRootPlusFromRoundedMinusDiscriminantSqrt_abs_error_le`, `flQuadraticRootsByBSignRoundedDiscriminantSqrt_abs_error_le`, `quadraticOverflowExample_b_square_single_finiteOverflowRange`, `quadraticOverflowExample_scaled_b_square_single_finiteNormalRange`, `quadraticOverflowExample_scaled_four_ac_single_finiteNormalRange`, `quadraticOverflowExample_scaled_discriminant_single_finiteNormalRange`, `quadraticOverflowExample_roots`, `quadraticScaledOverflowExample_variable_scaling` |
| Quadratic mixed-precision discriminant path | Higham §1.8 | `flQuadraticDiscriminantAbsErrorBound_eq_poly`, `flQuadraticDiscriminantAbsErrorBound_le_of_u_le`, `flQuadraticDiscriminantAbsErrorBound_le_of_simulatesHigherPrecision`, `flQuadraticRootPlusMixedDiscriminantSqrt_abs_error_le`, `flQuadraticRootMinusMixedDiscriminantSqrt_abs_error_le` |
| Quadratic displayed double finite-range discriminant path | Higham §1.8 | `quadraticOverflowExample_b_square_double_finiteNormalRange`, `quadraticOverflowExample_four_a_double_finiteNormalRange`, `quadraticOverflowExample_four_ac_double_finiteNormalRange`, `quadraticOverflowExample_discriminant_double_finiteNormalRange`, `quadraticOverflowExample_discriminant_path_double_finiteNormalRange` |
| Quadratic displayed double exact-primitive round-to-even path | Higham §1.8 | `quadraticOverflowExample_b_square_double_roundToEvenOp_standardModel`, `quadraticOverflowExample_four_a_double_roundToEvenOp_standardModel`, `quadraticOverflowExample_four_ac_double_roundToEvenOp_standardModel`, `quadraticOverflowExample_discriminant_sub_double_roundToEvenOp_standardModel`, `quadraticOverflowExample_exact_discriminant_path_double_ieeeRoundToNearestEvenOpResult_noFlags` |
| Quadratic displayed double rounded-intermediate round-to-even path | Higham §1.8 | `quadraticOverflowExample_b_square_doubleRounded`, `quadraticOverflowExample_four_a_doubleRounded`, `quadraticOverflowExample_four_ac_doubleRounded`, `quadraticOverflowExample_discriminant_doubleRounded`, `quadraticOverflowExample_discriminant_path_doubleRounded_finiteNormalRange`, `quadraticOverflowExample_discriminant_path_doubleRounded_roundToEvenOp_standardModel`, `quadraticOverflowExample_discriminant_path_doubleRounded_ieeeRoundToNearestEvenOpResult_noFlags`, `quadraticOverflowExample_discriminant_path_doubleRounded_ieeeRoundToNearestEvenOpResult_toReal` |
| Kahan-Muller recurrence exact, four-significant display trace, and instability algebra | Higham Problem 1.8 | `mullerExact_satisfies_recurrence`, `mullerExact_lt_succ`, `mullerExact_tendsto_six`, `problem_1_8_x34_rounds_to_5_998`, `mullerDecimal4Trace_rounding_intervals`, `mullerDecimal4Trace_34_eq_100`, `mullerDecimal4Trace_34_abs_error_gt_94`, `mullerModeY_linear_recurrence`, `mullerModeRatio_eq_hundred_sub`, `mullerModeRatio_gt_99_of_dominant` |
| Sample variance exact algebra, aggregate cancellation, condition-number closed forms, perturbed-mean identity, and update rounding bounds | Higham §1.9, Problems 1.7 and 1.10 | `sampleVarianceTwoPass_eq_onePass`, `sampleVarianceShiftedOnePass_eq_twoPass`, `prefixMean_succ`, `prefixCorrectedSumSquares_succ`, `flPrefixMeanStep_eq_exact_with_local_errors`, `flPrefixMeanStep_abs_error_le`, `flPrefixMeanStep_abs_error_le_prefixMean_succ`, `prefixMeanStepExact_prefixMean_eq_succ`, `prefixMeanStepExact_sub_prefixMeanStepExact`, `flPrefixMeanTrajectoryAbsErrorBudget_nonneg`, `flPrefixMeanTrajectory_abs_error_le_budget`, `flPrefixCorrectedSumSquaresStep_eq_exact_with_local_errors`, `flPrefixCorrectedSumSquaresStep_abs_error_le`, `flPrefixCorrectedSumSquaresStep_abs_error_le_prefix_succ`, `prefixCorrectedSumSquaresStepExact_prefix_eq_succ`, `prefixCorrectedSumSquaresStepExact_abs_sub_le`, `flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget_nonneg`, `flPrefixCorrectedSumSquaresTrajectory_abs_error_le_budget`, `flSampleVarianceUpdateAbsErrorBudget_nonneg`, `flSampleVarianceUpdate_abs_error_le_budget`, `prefixMean_example_values_10000_10001_10002`, `prefixCorrectedSumSquares_example_values_10000_10001_10002`, `sampleVarianceUpdate_example_10000_10001_10002`, `sampleVarianceTwoPass_nonneg`, `sampleVarianceOnePassAggregates_cancelled_relError_example_10000_10001_10002`, `sampleVarianceOnePassAggregates_neg_of_sumSq_lt`, `sampleVarianceOnePassAggregates_negative_example_10000_10001_10002`, `sampleMean_add_scaled`, `sampleVarianceTwoPass_add_scaled_sub_eq`, `sampleVarianceDirectionalCoeff_componentwise_le`, `sampleVarianceDirectionalCoeff_normwise_le`, `sampleVarianceKappaNClosed_eq_expanded`, `sampleVarianceKappaCClosed_le_KappaNClosed`, `flSampleMean_backward_error`, `flSampleMean_abs_error_le_gamma`, `sampleMean_deviation_sum_eq_zero`, `sum_sq_sub_perturbedMean_eq_sum_sq_sub_sampleMean_add`, `sampleVarianceTwoPassWithMean_eq_twoPass_add`, `sampleVarianceTwoPassWithMean_relError_eq_quadratic`, `sampleVarianceTwoPassWithMean_mul_one_add_relError_le`, `exists_weightedRelativeErrorFactor_of_nonneg_sum`, `flSquaredDeviationWithMean_eq_mul_one_add_gamma3`, `flSampleVarianceTwoPassWithMean_eq_mul_one_add_gamma`, `flSampleVarianceTwoPass_relError_le_gamma_add_mean_quadratic`, `flSampleVarianceTwoPass_mean_quadratic_le_gamma_sq`, `flSampleVarianceTwoPass_relError_le_gamma_add_gamma_sq_mean_bound`, `gamma_eq_linear_plus_quadratic_remainder`, `flSampleVarianceTwoPass_relError_le_linear_u_add_explicit_remainder` |
| Sample variance concrete binary32 one-pass trace skeleton | Higham §1.9 | `sampleVarianceOnePassIeeeSingleRoundingCertificate`, `sampleVarianceOnePassIeeeSingle_sourceRoundingEvidenceCertificate`, `sampleVarianceOnePassIeeeSingle_sq0_eq`, `sampleVarianceOnePassIeeeSingle_sq1_eq`, `sampleVarianceOnePassIeeeSingle_sq2_eq`, `sampleVarianceOnePassIeeeSingle_sum01_eq`, `sampleVarianceOnePassIeeeSingle_sum_eq`, `sampleVarianceOnePassIeeeSingle_sumSq_eq_of_sq1_sq2`, `sampleVarianceOnePassIeeeSingle_sumSq_eq_of_sq2`, `sampleVarianceOnePassIeeeSingle_sumSq_eq`, `sampleVarianceOnePassIeeeSingle_sumSquare_eq`, `sampleVarianceOnePassIeeeSingle_meanSquareTerm_eq`, `sampleVarianceOnePassIeeeSingleRoundingCertificate_of_sq2_eq`, `sampleVarianceOnePassIeeeSingleRoundingCertificate_closed`, `sampleVarianceOnePassIeeeSingleTrace_zero_of_sq2_eq`, `sampleVarianceOnePassIeeeSingleTrace_relError_one_of_sq2_eq`, `sampleVarianceOnePassIeeeSingleTrace_zero`, `sampleVarianceOnePassIeeeSingleTrace_relError_one` |
| Cramer's rule and GEPP 2-by-2 residual bridge | Higham §1.10.1, Problem 1.9 | `cramer2x2_first_eq`, `cramer2x2_second_eq`, `cramer2x2Solution_solves`, `cramer2x2Inverse_isInverse`, `flDet2x2_error_le_gamma3`, `cramer2x2Solution_error_from_flNumerators_exact_den`, `cramer2x2Solution_relative_forward_error_from_flNumerators_exact_den_condAt`, `cramer2x2Residual_infNorm_from_flNumerators_exact_den_condInv`, `gepp2_relativeResidual2_le_wilkinson` |
| Accumulation, compensated `log(1+x)`, and log-exp finite-`n` approximation | Higham §1.11, Problem 1.5 | `logOnePlusCompensatedExact`, `logOnePlusCompensatedExact_eq_log_one_add`, `logOnePlusCompensatedPerturbedNonbranch_exact_w_signedRelErrorWitness`, `logOnePlusCompensatedPerturbedNonbranch_exact_w_relError_eq`, `logOnePlusCompensatedPerturbedNonbranch_exact_w_relError_le`, `expOneApproxRoundedBase_eq_exact_base_mul_initial_error_pow`, `expOneApproxLogExpExact_eq_exact_base`, `expOneApproxLogExpWithLogRelError_eq_exact_base_mul_exp`, `expOneApproxLogExp_logRelError_exponent_abs_le`, `expOneApproxLogExpRoundedOuter_eq_exact_base_mul_exp_mul`, `expOneApproxLogExpRoundedOuter_relError_le_fp` |
| Instability without cancellation exact baselines and local single-precision drop-off | Higham §1.12.1--§1.12.3 | `noPivotExample_kappaInf_eq`, `noPivotRoundedLU_error_matrix`, `noPivotIeeeSingle_add_one_inv_epsilon_rounds_to_inv`, `noPivotIeeeSingleSmallEpsilon_error_matrix`, `noPivotPartialPivotLUFactSpec`, `noPivotPartialPivotLUBackwardError_zero`, `noPivotIeeeSingle_partialPivot_div_epsilon_one_rounds_to_epsilon`, `noPivotIeeeSingle_partialPivot_mul_epsilon_one_rounds_to_epsilon`, `noPivotIeeeSingle_partialPivot_sub_neg_one_epsilon_rounds_to_neg_one`, `noPivotIeeeSinglePartialPivotRoundedLUBackwardError`, `noPivotPartialPivot_multiplier_abs_le_one`, `repeatedSquare_repeatedSqrt_sixty_eq_self`, `hp48gSqrtSquareSurrogate_relError_100`, `hp48gSqrtSquareSurrogate_absError_of_ge_one`, `hp48gSqrtSquareSurrogate_relError_of_ge_one`, `hp48gSqrtSquareSurrogate_absError_of_nonneg_lt_one`, `hp48gSqrtSquareSurrogate_relError_of_pos_lt_one`, `inverseSquareTerm_le_two_pow_neg_24_of_ge`, `inverseSquareTerm_between_half_ulp_and_one_ulp_of_ge_2897_lt_4096`, `inverseSquareSingle_add_term_rounds_to_next_of_half_ulp_lt`, `inverseSquareSingle_add_term_rounds_to_next_of_index_range`, `inverseSquareSingle_add_term_rounds_to_nearest_mantissa_of_scaled_bounds`, `inverseSquareSingleForwardStep_eq_left_of_adjacent_strict_between_left_closer`, `inverseSquareSingleForwardStep_eq_right_of_adjacent_strict_between_right_closer`, `inverseSquareSingleForwardStep_normalizedValue_nearest_mantissa_of_scaled_bounds_at_scale`, `inverseSquareSingleEarlyMantissaPrefix_2895_eq`, `inverseSquareSingleEarlyMantissaPrefix_2895_add_base_eq_preWindow`, `inverseSquareSingleEarlyMantissaIncrementNearestCertificateBool_eq_true`, `inverseSquareSingleEarlyMantissaIncrementNearestCertificate`, `inverseSquareSingleForwardAccumulator_one_eq_one`, `inverseSquareSingleEarlyMantissaIncrementRule_closed`, `inverseSquareSingleForwardAccumulator_2896_eq_prePlateauWindowStart`, `inverseSquareSingleForwardAccumulator_2896_eq_prePlateauWindowStart_of_early_mantissa_increment_rule`, `inverseSquareSingleForwardAccumulatorFrom_normalizedValue_of_index_window`, `inverseSquareSingleForwardAccumulatorFrom_prePlateauWindowStart_2897_of_le_1194`, `inverseSquareSingleForwardAccumulatorFrom_prePlateauWindowStart_2897_1194_eq_sixBeforePlateau`, `inverseSquareSingleForwardAccumulatorFrom_prePlateauWindowStart_2897_lt_plateau_of_lt_1200`, `inverseSquareSingleForwardAccumulatorFrom_sixBeforePlateau_4091_six_add_eq_plateau`, `inverseSquareSingleForwardAccumulatorFrom_prePlateauWindowStart_2897_1200_add_eq_plateau`, `inverseSquareSingleForwardAccumulator_4096_add_eq_plateau_of_2896_eq_prePlateauWindowStart`, `inverseSquareSingleForwardAccumulator_2896_add_lt_plateau_of_2896_eq_prePlateauWindowStart`, `inverseSquareSingleForwardAccumulator_4096_add_eq_plateau_of_early_mantissa_increment_rule`, `inverseSquareSingleForwardAccumulator_2896_add_lt_plateau_of_early_mantissa_increment_rule`, `inverseSquareSingleForwardAccumulator_4096_add_eq_plateau`, `inverseSquareSingleForwardAccumulator_2896_add_lt_plateau`, `inverseSquareSingleReverseAccumulatorFrom_add`, `inverseSquareSingleReverseAccumulator_ten_pow_nine_split_4096`, `inverseSquareSingleSixBeforePlateau_add_4091_term_rounds_to_fiveBeforePlateau`, `inverseSquareSingleFiveBeforePlateau_add_4092_term_rounds_to_fourBeforePlateau`, `inverseSquareSingleFourBeforePlateau_add_4093_term_rounds_to_threeBeforePlateau`, `inverseSquareSingleThreeBeforePlateau_add_4094_term_rounds_to_twoBeforePlateau`, `inverseSquareSingleTwoBeforePlateau_add_4095_term_rounds_to_prePlateau`, `inverseSquareSinglePrePlateau_add_4096_term_rounds_to_plateau`, `inverseSquareSinglePlateau_add_4096_term_rounds_to_self`, `inverseSquareSinglePlateau_add_term_rounds_to_self_of_ge_4096` |
| Reverse inverse-square high-prefix exact mass bridge and printed-value certificate reduction | Higham §1.12.3 | `inverseSquareExactReverseAccumulatorFrom`, `inverseSquareExactReverseAccumulator`, `inverseSquareExactReverseAccumulatorFrom_add`, `inverseSquareExactReverseAccumulator_ten_pow_nine_split_4096`, `inverseSquareExactReverseAccumulator_ten_pow_nine_eq_highPrefix_add_low4096`, `inverseSquareSingleReversePrintedAccumulator`, `inverseSquareSingleReverseSuffixStartLower`, `inverseSquareSingleReverseSuffixStartUpper`, `inverseSquareSingleReverseSuffixStartUpperTight`, `inverseSquareTerm_le_telescope`, `inverseSquareTerm_ge_telescope_succ`, `inverseSquareExactReverseAccumulatorFrom_le_telescope`, `inverseSquareExactReverseAccumulatorFrom_ge_telescope_succ`, `inverseSquareExactReverseTenPowNineHighPrefix_le_inv_4096`, `inverseSquareExactReverseAccumulator_ten_pow_nine_sub_low4096_le_inv_4096`, `inverseSquareExactReverseTenPowNineHighPrefix_mem_printedSuffixStartWindow`, `inverseSquareExactReverseTenPowNineHighPrefix_mem_printedSuffixStartTightWindow`, `inverseSquareExactReverseAccumulator_ten_pow_nine_sub_low4096_mem_printedSuffixStartWindow`, `inverseSquareSingleReverseTenPowNineHighPrefixState`, `inverseSquareSingleReverseTenPowNineHighPrefixCandidate`, `inverseSquareSingleReverseAfter4096Candidate`, `inverseSquareSingleReverseAfter4095Candidate`, `inverseSquareSingleReverseBefore2048Candidate`, `inverseSquareSingleReverseAfter2048Candidate`, `inverseSquareSingleReverseBefore1024Candidate`, `inverseSquareSingleReverseTenPowNineHighPrefixCandidate_mem_printedSuffixStartWindow`, `inverseSquareSingleReverseTenPowNineHighPrefixCandidate_mem_printedSuffixStartTightWindow`, `inverseSquareSingleForwardStep_eq_left_of_adjacent_strict_between_left_closer`, `inverseSquareSingleForwardStep_eq_right_of_adjacent_strict_between_right_closer`, `inverseSquareSingleForwardStep_normalizedValue_nearest_mantissa_of_scaled_bounds_at_scale`, `inverseSquareSingleReverseAccumulatorFrom_scaledBandPrefix_of_le`, `inverseSquareSingleReverseCandidate_add_4096_term_rounds_to_after4096`, `inverseSquareSingleReverseAfter4096_add_4095_term_rounds_to_after4095`, `inverseSquareSingleReverseAfter4095Prefix_4094_to_2049_eq`, `inverseSquareSingleReverseAfter4095Band4094To2049CertificateBool_eq_true`, `inverseSquareSingleReverseAfter4095Band4094To2049Certificate`, `inverseSquareSingleReverseAfter4095Accumulator_4094_to_before2048`, `inverseSquareSingleReverseBefore2048_add_2048_term_rounds_to_after2048`, `inverseSquareSingleReverseAfter2048Prefix_2047_to_1025_eq`, `inverseSquareSingleReverseAfter2048Band2047To1025CertificateBool_eq_true`, `inverseSquareSingleReverseAfter2048Band2047To1025Certificate`, `inverseSquareSingleReverseAfter2048Accumulator_2047_to_before1024`, `inverseSquareSingleReverseTenPowNineHighPrefixEqCandidate`, `inverseSquareSingleReverseCandidateSuffixMapsToPrinted`, `inverseSquareSingleReverseAfter4096SuffixMapsToPrinted`, `inverseSquareSingleReverseAfter4095SuffixMapsToPrinted`, `inverseSquareSingleReverseBefore2048SuffixMapsToPrinted`, `inverseSquareSingleReverseBefore1024SuffixMapsToPrinted`, `inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixWindow`, `inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow`, `inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixWindow_of_eq_candidate`, `inverseSquareSingleReverseTenPowNineHighPrefixInPrintedSuffixTightWindow_of_eq_candidate`, `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_candidate_certificates`, `inverseSquareSingleReverseCandidateSuffixMapsToPrinted_of_after4096`, `inverseSquareSingleReverseAfter4096SuffixMapsToPrinted_of_after4095`, `inverseSquareSingleReverseAfter4095SuffixMapsToPrinted_of_before2048`, `inverseSquareSingleReverseBefore2048SuffixMapsToPrinted_of_before1024`, `inverseSquareSingleReverseSuffixWindowMapsToPrinted`, `inverseSquareSingleReverseTightSuffixWindowMapsToPrinted`, `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_window_certificates`, `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_tight_window_certificates` |
| Reverse inverse-square after-`1024` compact suffix continuation | Higham §1.12.3 | `inverseSquareSingleReverseAfter1024Candidate`, `inverseSquareSingleReverseBefore512Candidate`, `inverseSquareSingleReverseBefore1024_add_1024_term_rounds_to_after1024`, `inverseSquareSingleReverseAfter1024Prefix_1023_to_513_eq`, `inverseSquareSingleReverseAfter1024Band1023To513CertificateBool_eq_true`, `inverseSquareSingleReverseAfter1024Band1023To513Certificate`, `inverseSquareSingleReverseAfter1024Accumulator_1023_bandPrefix_of_le`, `inverseSquareSingleReverseAfter1024Accumulator_1023_to_before512`, `inverseSquareSingleReverseBefore512SuffixMapsToPrinted`, `inverseSquareSingleReverseBefore1024SuffixMapsToPrinted_of_before512` |
| Reverse inverse-square after-`512` compact suffix continuation | Higham §1.12.3 | `inverseSquareSingleReverseAfter512Candidate`, `inverseSquareSingleReverseBefore256Candidate`, `inverseSquareSingleReverseBefore512_add_512_term_rounds_to_after512`, `inverseSquareSingleReverseAfter512Prefix_511_to_257_eq`, `inverseSquareSingleReverseAfter512Band511To257CertificateBool_eq_true`, `inverseSquareSingleReverseAfter512Band511To257Certificate`, `inverseSquareSingleReverseAfter512Accumulator_511_bandPrefix_of_le`, `inverseSquareSingleReverseAfter512Accumulator_511_to_before256`, `inverseSquareSingleReverseBefore256SuffixMapsToPrinted`, `inverseSquareSingleReverseBefore512SuffixMapsToPrinted_of_before256` |
| Reverse inverse-square after-`256` compact suffix continuation | Higham §1.12.3 | `inverseSquareSingleReverseAfter256Candidate`, `inverseSquareSingleReverseBefore128Candidate`, `inverseSquareSingleReverseBefore256_add_256_term_rounds_to_after256`, `inverseSquareSingleReverseAfter256Prefix_255_to_129_eq`, `inverseSquareSingleReverseAfter256Band255To129CertificateBool_eq_true`, `inverseSquareSingleReverseAfter256Band255To129Certificate`, `inverseSquareSingleReverseAfter256Accumulator_255_bandPrefix_of_le`, `inverseSquareSingleReverseAfter256Accumulator_255_to_before128`, `inverseSquareSingleReverseBefore128SuffixMapsToPrinted`, `inverseSquareSingleReverseBefore256SuffixMapsToPrinted_of_before128` |
| Reverse inverse-square after-`128` compact suffix continuation | Higham §1.12.3 | `inverseSquareSingleReverseAfter128Candidate`, `inverseSquareSingleReverseBefore64Candidate`, `inverseSquareSingleReverseBefore128_add_128_term_rounds_to_after128`, `inverseSquareSingleReverseAfter128Prefix_127_to_65_eq`, `inverseSquareSingleReverseAfter128Band127To65CertificateBool_eq_true`, `inverseSquareSingleReverseAfter128Band127To65Certificate`, `inverseSquareSingleReverseAfter128Accumulator_127_bandPrefix_of_le`, `inverseSquareSingleReverseAfter128Accumulator_127_to_before64`, `inverseSquareSingleReverseBefore64SuffixMapsToPrinted`, `inverseSquareSingleReverseBefore128SuffixMapsToPrinted_of_before64` |
| Reverse inverse-square after-`64` compact suffix continuation | Higham §1.12.3 | `inverseSquareSingleReverseAfter64Candidate`, `inverseSquareSingleReverseBefore32Candidate`, `inverseSquareSingleReverseBefore64_add_64_term_rounds_to_after64`, `inverseSquareSingleReverseAfter64Prefix_63_to_33_eq`, `inverseSquareSingleReverseAfter64Band63To33CertificateBool_eq_true`, `inverseSquareSingleReverseAfter64Band63To33Certificate`, `inverseSquareSingleReverseAfter64Accumulator_63_bandPrefix_of_le`, `inverseSquareSingleReverseAfter64Accumulator_63_to_before32`, `inverseSquareSingleReverseBefore32SuffixMapsToPrinted`, `inverseSquareSingleReverseBefore64SuffixMapsToPrinted_of_before32` |
| Reverse inverse-square after-`32` through final concrete suffix closure | Higham §1.12.3 | `inverseSquareSingleReverseAfter32Candidate`, `inverseSquareSingleReverseBefore16Candidate`, `inverseSquareSingleReverseAfter16Candidate`, `inverseSquareSingleReverseBefore8Candidate`, `inverseSquareSingleReverseAfter8Candidate`, `inverseSquareSingleReverseBefore4Candidate`, `inverseSquareSingleReverseAfter4Candidate`, `inverseSquareSingleReverseAfter3Candidate`, `inverseSquareSingleReverseAfter2Candidate`, `inverseSquareSingleReverseBefore32_add_32_term_rounds_to_after32`, `inverseSquareSingleReverseAfter32Accumulator_31_to_before16`, `inverseSquareSingleReverseBefore16_add_16_term_rounds_to_after16`, `inverseSquareSingleReverseAfter16Accumulator_15_to_before8`, `inverseSquareSingleReverseBefore8_add_8_term_rounds_to_after8`, `inverseSquareSingleReverseAfter8Accumulator_7_to_before4`, `inverseSquareSingleReverseBefore4SuffixMapsToPrinted_closed`, `inverseSquareSingleReverseBefore32SuffixMapsToPrinted_closed`, `inverseSquareSingleReverseCandidateSuffixMapsToPrinted_closed`, `inverseSquareSingleReverseAccumulator_ten_pow_nine_eq_printed_of_highPrefix_eq_candidate` |
| Increasing-precision micro-examples | Higham §1.13 | `increasingPrecisionSinExampleSource_perturbation_abs_le`, `increasingPrecisionExampleExactZ_two_thirds_eq_one`, `increasingPrecisionExampleElse_relError_one_of_expHat_one` |
| Cancellation of rounding errors Algorithm 2 baseline | Higham §1.14.1 | `expm1Algorithm2Exact_eq_algorithm1Exact`, `expm1Table12_x_rows`, `expm1Table12_algorithm1_rows`, `expm1Table12_algorithm2_rows`, `expm1Table12_algorithm2_ten_pow_neg15_last_digit_correction`, `expm1Page23_displayed_single_precision_ratio`, `expm1Page23_displayed_exact_arithmetic_ratio`, `expm1LogRatio_tendsto_one`, `expm1Log_one_add_sub_linear_quadratic_abs_le`, `expm1LogRatio_one_add_eq_inv_one_sub_half_add_remainder`, `expm1LogRatio_one_add_sub_one_add_half_abs_le`, `expm1LogRatio_sub_one_abs_le`, `expm1LogRatio_self_sub_abs_le`, `expm1LogRatio_one_add_diff_sub_half_abs_le`, `expm1LogRatio_mul_one_add_delta_diff_sub_y_delta_half_abs_le`, `expm1LogRatio_mul_one_add_delta_diff_sub_delta_half_abs_le`, `expm1LogRatio_mul_one_add_delta_diff_sub_logRatio_delta_half_abs_le`, `expm1Algorithm2RoundedCore_eq_source_1_9`, `expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma4` |
| Givens rotation displayed block and rectangular/economy QR handoff | Higham §1.14.2 | `givensRotation_trig_orthogonal`, `givensQRRectangularRotationCount_ten_by_six`, `rectangular_givens_qr_backward_ten_by_six_unit_roundoff`, `RectangularQRFactorPerturbationBound`, `RectangularQRFactorStewartRelativeBound`, `EconomyQRFactorStewartRelativeBound`, `rectangular_givens_qr_backward_ten_by_six_unit_roundoff_qr_factor_relative_error`, `rectangular_givens_qr_backward_ten_by_six_unit_roundoff_qr_factor_relative_error_of_stewart`, `rectangular_givens_qr_backward_ten_by_six_unit_roundoff_economy_qr_factor_relative_error_of_stewart`, `qrTenBySixStewartRelativeRadius_le_of_unitRoundoff_le_smallRadius_div`, `rectangular_givens_qr_backward_ten_by_six_unit_roundoff_economy_qr_factor_relative_error_of_stewart_condition_surfaces_linear_u_of_unitRoundoff_le_smallRadius_div` |
Stewart 1977 QR perturbation infrastructure also includes the last-column
Frobenius-inverse handoff
`StewartQRLinearInverseBound.lastColumn_step_of_right_inverse_frob_source_constant_factor_le`,
which converts a source-shaped Frobenius bound on the leading-block right
inverse into the operator certificate required by the recursive solve.  The
remaining source proof obligation is the scalar coefficient inequality that
absorbs the visible last-column factor into `n(2+sqrt(2))kappa`.

| Beneficial rounding power-method exact example | Higham §1.15 | `beneficialPowerCharDet_eq`, `beneficialPowerCharDet_root_small`, `beneficialPowerCharDet_root_dominant`, `beneficialPowerEigenvalueSmall_display_accuracy`, `beneficialPowerMatrixIeeeDoubleRounded_eq_explicit`, `beneficialPowerMatrixIeeeDoubleRounded_entrywise_abs_error_le_two_pow_neg53`, `beneficialPowerMatrixIeeeDoubleRounded_firstStep_vecNorm2_le_sqrt_three_mul_three_two_pow_neg53`, `beneficialPowerMatrixIeeeDoubleRounded_det_ne_zero`, `beneficialPowerMatrixIeeeDoubleRoundedCharDet_zero_ne`, `beneficialPowerMatrixIeeeDoubleRoundedCharDet_eq`, `beneficialPowerMatrixIeeeDoubleRoundedCharDet_117_100_pos`, `beneficialPowerMatrixIeeeDoubleRoundedCharDet_continuous`, `beneficialPowerMatrixIeeeDoubleRoundedCharDet_exists_root_neg_one_e14_zero`, `beneficialPowerMatrixIeeeDoubleRoundedCharDet_exists_root_neg_one_e17_zero`, `beneficialPowerMatrixIeeeDoubleRoundedCharDet_exists_root_439_1000_11_25`, `beneficialPowerMatrixIeeeDoubleRoundedCharDet_exists_root_29_25_117_100`, `beneficialPowerMatrixIeeeDoubleRoundedCharDet_existsUnique_root_neg_one_e14_zero`, `beneficialPowerMatrixIeeeDoubleRoundedCharDet_existsUnique_root_439_1000_11_25`, `beneficialPowerMatrixIeeeDoubleRoundedCharDet_existsUnique_root_29_25_117_100`, `beneficialPowerMatrixIeeeDoubleRoundedCharRoot_two_tail_spectral_ratio_le_half`, `beneficialPowerMatrixIeeeDoubleRoundedCharDet_exists_three_bracketed_roots_tail_ratio_le_half`, `beneficialPowerMatrixIeeeDoubleRoundedCharRoot_dominant_isRightEigenpair_of_mem`, `beneficialPowerMatrixIeeeDoubleRoundedCharDet_exists_three_bracketed_roots_eigenpairs_tail_ratio_le_half`, `beneficialPowerMatrixIeeeDoubleRoundedCharDet_exists_three_bracketed_distinct_roots_eigenpairs_tail_ratio_le_half`, `beneficialPowerMatrixIeeeDoubleRoundedCharEigenvectorMatrix_det_ne_zero_of_bracketed_roots`, `beneficialPowerMatrixIeeeDoubleRoundedCharEigenvectorMatrix_isRightInverse_of_bracketed_roots`, `beneficialPowerMatrixIeeeDoubleRoundedCharDet_exists_three_bracketed_distinct_roots_eigenbasis_rightInverse_tail_ratio_le_half`, `beneficialPowerMatrixIeeeDoubleRoundedCharDet_exists_three_bracketed_distinct_roots_eigenbasis_coefficients_tail_ratio_le_half`, `beneficialPowerMatrixIeeeDoubleRoundedCharStartReplacement_det_lt_zero_of_tight_small_mid`, `beneficialPowerStoredStart_exists_dominant_component_certificate`, `beneficialPowerStoredStartDominantComponentCert`, `beneficialPowerStoredStartDominantComponentCert_q_eq`, `beneficialPowerStoredStart_scaled_residual_tendsto_zero`, `beneficialPowerFirstStep_perturbed_eq_delta` |
| Beneficial rounding inverse-iteration local handoff | Higham §1.15 | `inverseIteration_nonTarget_shift_gap_of_eigenvalue_gap_and_target_radius`, `inverseIteration_nonTarget_shift_gap_of_uniform_eigenvalue_gap_and_target_radius`, `IsOrthogonal.column_vecNorm2_eq_one`, `IsOrthogonal.column_vecNorm2_le_one`, `inverseIteration_eigenvector_norm_le_one_of_orthogonal_columns`, `inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_backward_error_orthogonal_eigenbasis_residual_gap_absolute`, `inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_backward_error_orthogonal_eigenbasis_residual_gap_absolute_of_A_norm_nonneg`, `inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_backward_error_orthogonal_eigenbasis_residual_eigengap_absolute`, `inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_backward_error_orthogonal_eigenbasis_residual_eigengap_absolute_of_A_norm_nonneg`, `inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_backward_error_orthogonal_eigenbasis_opNorm_eigengap_absolute`, `inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_backward_error_orthogonal_eigenbasis_opNorm_eigengap_absolute_of_A_norm_nonneg`, `inverseIteration_shiftedSolve_near_parallel_decomposition_of_relative_residual_orthogonal_eigenbasis_eigengap_absolute`, `inverseIteration_shiftedSolve_eigenResidual_norm_le_of_relative_residual_orthogonal_eigenbasis_eigengap_absolute_of_A_norm_nonneg` |
| Beneficial rounding inverse-iteration normalized tail handoff | Higham §1.15 | `inverseIteration_shiftedSolve_near_parallel_decomposition_of_relative_residual_orthogonal_eigenbasis_eigengap_relative_tail`, `inverseIteration_shiftedSolve_eigenResidual_norm_le_of_relative_residual_orthogonal_eigenbasis_eigengap_relative_tail_of_A_norm_nonneg`, `inverseIteration_relative_tail_le_of_pred_mul_rho_le_eps_mul_sep`, `inverseIteration_relative_tail_le_of_rho_le_eps_mul_sep_div_pred` |
| Beneficial rounding inverse-iteration LU shifted-solve route | Higham §1.15, §9.4 | `inverseIteration_lu_shiftedSolve_residual_norm_le_of_component_frob_budget`, `inverseIteration_lu_shiftedSolve_near_parallel_decomposition_of_component_frob_budget_orthogonal_eigenbasis_eigengap_relative_tail`, `inverseIteration_lu_shiftedSolve_eigenResidual_norm_le_of_component_frob_budget_orthogonal_eigenbasis_eigengap_relative_tail_of_A_norm_nonneg`, `inverseIteration_lu_shiftedSolve_near_parallel_decomposition_of_component_frob_budget_orthogonal_eigenbasis_eigengap_relative_tail_of_residual_gap_cap`, `inverseIteration_lu_shiftedSolve_eigenResidual_norm_le_of_component_frob_budget_orthogonal_eigenbasis_eigengap_relative_tail_of_residual_gap_cap_of_A_norm_nonneg` |
| Problem-dependent stability upper-Hessenberg exact example | Higham §1.16 | `hessenbergDiagRoundedStep_eq_perturbed_exactStep`, `hessenbergDetRoundedProduct_relError_le_gamma`, `hessenbergDetExample_isUpperHessenberg`, `hessenbergDetExample_mul_ones`, `hessenbergDetExampleMatrixInv_alpha_ten_pow_isInverse`, `hessenbergDetExample_kappaInfProduct_alpha_ten_pow_eq`, `hessenbergDetExample_kappaInfProduct_alpha_ten_pow_near_sixteen`, `hessenbergDetExampleNoPivotU_det_eq_diag_prod`, `hessenbergDetExampleNoPivotUDiag_prod_eq`, `hessenbergDetExampleMatrix_det_eq_noPivotUDiag_prod`, `hessenbergDetExampleMatrix_det_eq`, `hessenbergDetExampleMatrix_alpha_ten_pow_det_eq`, `hessenbergDetExampleMatrix_alpha_ten_pow_det_near_two`, `hessenbergDetExample_alpha_ten_pow_exact_table_baseline`, `hessenbergDetExampleFirstMultiplier_alpha_ten_pow` |
| Nonrandom rounding Horner rational-function setup | Higham §1.17 | `kahanHornerNumerator_eq_poly`, `kahanHornerDenominator_eq_poly`, `kahanHornerGridPoint_pairwise_distance_le_source_width`, `kahanHornerDenominator_grid_pos_of_one_le_of_le_three_sixty_one`, `kahanRationalFunction_first_to_last_variation_lt` |
| γ-function | Higham §3.1, §3.4 | `gamma`, `gamma_eq_linear_plus_quadratic_remainder`, `prod_error_bound`, `prod_signed_error_bound`, `relErrorCounter`, `relErrorCounter_abs_sub_one_le_gamma`, `relErrorCounter_mul`, `relErrorCounter_div`, `gamma_mul`, `gamma_inv`, `gamma_div_le_branch`, `gamma_div_gt_branch`, `gamma_div` |
| Small-`nu` product bound | Higham §3.4, Lemma 3.4 and Problem 3.2 | `prod_one_add_delta_eq_one_add_eta_bound_101`, `prod_one_add_delta_eq_one_add_eta_bound_101_le`, `prod_one_add_delta_eq_one_add_phi_bound_problem32`, `prod_one_add_delta_abs_sub_one_le_exp_sub_one`, `real_exp_sub_one_lt_div_one_sub_half_of_pos_of_lt_two` |
| Relative precision notation | Higham §3.4 | `relPrecision`, `relPrecision_symm`, `relPrecision_trans`, `pryceOne_iff`, `relPrecision_same_sign_of_nonzero` |
| Rounded complex arithmetic | Higham §3.6, Lemma 3.5; §25.8 formula (25.1) | `complexRelErrorModel`, `fl_complexAdd_rel_error_model`, `fl_complexSub_rel_error_model`, `fl_complexMul_rel_error_model`, `fl_complexDiv_rel_error_model`, `smithComplexDivBranchCExact_eq_div`, `smithComplexDivBranchDExact_eq_div`, `fl_smithComplexDivBranchC_rel_error_model`, `fl_smithComplexDivBranchD_rel_error_model`, `fl_smithComplexDiv_rel_error_model` — add/sub cases with radius `u`, multiplication with radius `sqrt(2)*gamma fp 2`, source-formula division with radius `sqrt(2)*gamma fp 4`, exact Smith branch algebra, and overflow-avoiding Smith division with radius `sqrt(2)*gamma fp 7` |
| Rank-one update error | Higham §3.7, Lemma 3.9 | `fl_rankOneUpdate_componentwise_error_bound`, `fl_rankOneUpdate_error_bound_vecNorm2` — concrete `fl(x-a(b^T x))` componentwise and Euclidean-norm bounds with `gamma fp (n+3)` |
| Summation error | Higham §3.1 | `sumSuffixErrorProduct`, `fl_sum_error_init_suffix_expansion`, `fl_sum_error`, `fl_sum_error_init`, `fl_sub_sum_error_init` |

Chapter 2 finite-zero, finite-range classification, tiny-underflow, fixed-exponent, one-slice, and global nonzero unbounded-rounding adapters: `FloatingPointFormat.finiteSystem_zero`, `FloatingPointFormat.nearestRoundingToFinite_zero`, `FloatingPointFormat.nearestRoundingToFinite_exact_signedRelErrorWitness`, `FloatingPointFormat.nearestRoundingToFinite_exact_signedRelErrorWitness_lt`, `FloatingPointFormat.exists_nearestRoundingToFinite_signedRelErrorWitness_zero`, `FloatingPointFormat.minNormalMagnitude`, `FloatingPointFormat.minSubnormalMagnitude`, `FloatingPointFormat.maxFiniteMagnitude`, `FloatingPointFormat.finiteNormalRange`, `FloatingPointFormat.finiteUnderflowRange`, `FloatingPointFormat.finiteOverflowRange`, `FloatingPointFormat.minNormalMagnitude_mem_finiteSystem`, `FloatingPointFormat.maxFiniteMagnitude_mem_finiteSystem`, `FloatingPointFormat.neg_minNormalMagnitude_mem_finiteSystem`, `FloatingPointFormat.neg_maxFiniteMagnitude_mem_finiteSystem`, `FloatingPointFormat.normalizedSystem_finiteNormalRange`, `FloatingPointFormat.normalizedSystem_abs_ge_minSubnormalMagnitude`, `FloatingPointFormat.subnormalSystem_finiteUnderflowRange`, `FloatingPointFormat.subnormalSystem_abs_ge_minSubnormalMagnitude`, `FloatingPointFormat.finiteSystem_zero_or_finiteNormalRange_or_finiteUnderflowRange`, `FloatingPointFormat.decimalSingleDigitFormat_finiteSystem_nine`, `FloatingPointFormat.decimalSingleDigitFormat_not_finiteSystem_eighteen`, `FloatingPointFormat.not_forall_finiteSystem_sub_finiteSystem`, `FloatingPointFormat.decimalSingleDigitTwoExponentFormat`, `FloatingPointFormat.decimalSingleDigitTwoExponentFormat_finiteSystem_one`, `FloatingPointFormat.decimalSingleDigitTwoExponentFormat_finiteSystem_ninety`, `FloatingPointFormat.decimalSingleDigitTwoExponentFormat_not_finiteSystem_eightynine`, `FloatingPointFormat.decimalSingleDigitTwoExponentFormat_round_add_one_ninety`, `FloatingPointFormat.finiteSystem_not_finiteOverflowRange`, `FloatingPointFormat.finiteSystem_abs_le_maxFiniteMagnitude`, `FloatingPointFormat.finiteSystem_ne_zero_abs_ge_minSubnormalMagnitude`, `FloatingPointFormat.nearestRoundingToFinite_output_zero_or_finiteNormalRange_or_finiteUnderflowRange`, `FloatingPointFormat.nearestRoundingToFinite_output_not_finiteOverflowRange`, `FloatingPointFormat.nearestRoundingToFinite_output_abs_le_maxFiniteMagnitude`, `FloatingPointFormat.nearestRoundingToFinite_maxFiniteMagnitude_of_gt_maxFiniteMagnitude`, `FloatingPointFormat.nearestRoundingToFinite_neg_maxFiniteMagnitude_of_lt_neg_maxFiniteMagnitude`, `FloatingPointFormat.finiteOverflowSaturation`, `FloatingPointFormat.finiteOverflowSaturation_nearestRoundingToFinite_of_finiteOverflowRange`, `FloatingPointFormat.nearestRoundingToFinite_eq_maxFiniteMagnitude_of_gt_maxFiniteMagnitude`, `FloatingPointFormat.nearestRoundingToFinite_eq_neg_maxFiniteMagnitude_of_lt_neg_maxFiniteMagnitude`, `FloatingPointFormat.nearestRoundingToFinite_eq_finiteOverflowSaturation_of_finiteOverflowRange`, `FloatingPointFormat.nearestRoundingToFinite_zero_of_abs_le_half_minSubnormalMagnitude`, `FloatingPointFormat.nearestRoundingToFinite_eq_zero_of_abs_lt_half_minSubnormalMagnitude`, `FloatingPointFormat.normalizedValue_false_minNormalMantissa_eq`, `FloatingPointFormat.normalizedValue_false_maxNormalMantissa_eq`, `FloatingPointFormat.exists_nearestRoundingToUnbounded_signedRelErrorWitness_powerInterval_positive`, `FloatingPointFormat.exists_nearestRoundingToUnbounded_signedRelErrorWitness_powerInterval_negative`, `FloatingPointFormat.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_powerInterval_positive`, `FloatingPointFormat.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_powerInterval_negative`, `FloatingPointFormat.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_powerInterval_positive`, `FloatingPointFormat.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_powerInterval_negative`, `FloatingPointFormat.exists_nearestRoundingToUnbounded_signedRelErrorWitness_powerBoundary_positive`, `FloatingPointFormat.exists_nearestRoundingToUnbounded_signedRelErrorWitness_powerBoundary_negative`, `FloatingPointFormat.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_powerBoundary_positive`, `FloatingPointFormat.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_powerBoundary_negative`, `FloatingPointFormat.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_powerBoundary_positive`, `FloatingPointFormat.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_powerBoundary_negative`, `FloatingPointFormat.exists_nearestRoundingToUnbounded_signedRelErrorWitness_powerSlice_positive`, `FloatingPointFormat.exists_nearestRoundingToUnbounded_signedRelErrorWitness_powerSlice_negative`, `FloatingPointFormat.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_powerSlice_positive`, `FloatingPointFormat.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_powerSlice_negative`, `FloatingPointFormat.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_powerSlice_positive`, `FloatingPointFormat.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_powerSlice_negative`, `FloatingPointFormat.exists_powerSliceExponent_positive`, `FloatingPointFormat.exists_powerSliceExponent_negative`, `FloatingPointFormat.exists_nearestRoundingToUnbounded_signedRelErrorWitness_nonzero`, `FloatingPointFormat.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_positive`, `FloatingPointFormat.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_negative`, `FloatingPointFormat.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_nonzero`, `FloatingPointFormat.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_positive`, `FloatingPointFormat.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_negative`, and `FloatingPointFormat.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_nonzero`.

Chapter 2 Problem 2.6 exact integer intervals: `FloatingPointFormat.integerIntervalRepresentable`, `FloatingPointFormat.problem2_6_ieeeSingle_largest_integer_interval`, and `FloatingPointFormat.problem2_6_ieeeDouble_largest_integer_interval` prove that the maximal contiguous integer ranges exactly representable in the finite-format models are `[-2^24,2^24]` for IEEE single and `[-2^53,2^53]` for IEEE double.

Chapter 2 Problem 2.3 normalized and subnormal branches: `FloatingPointFormat.problem2_3_sameExponentInteriorDoubleMantissas_card` and `FloatingPointFormat.problem2_3_boundaryInteriorDoubleMantissas_card` prove the `2^29 - 1` interior double-mantissa count for same-exponent and exponent-boundary normalized IEEE-single gaps, while `FloatingPointFormat.problem2_3_ieeeDouble_between_adjacent_ieeeSingle_sameExponent_signed` and `FloatingPointFormat.problem2_3_ieeeDouble_between_adjacent_ieeeSingle_boundary_signed` prove those interior mantissas are finite IEEE-double values strictly between the signed adjacent normalized endpoints. The subnormal block theorem `FloatingPointFormat.problem2_3_ieeeDouble_between_ieeeSingle_subnormal_block_signed` proves that a single-subnormal grid step in dyadic block `s` has listed interior double mantissas at scale `2^(52-s)`; `FloatingPointFormat.problem2_3_exists_subnormalBlock_of_ieeeSingle_subnormalMantissa` and `FloatingPointFormat.problem2_3_exists_adjacentSingleGap_of_ieeeSingle_subnormalMantissa` prove every positive IEEE-single subnormal mantissa belongs to such a signed branch-family block. The normalized coverage theorems `FloatingPointFormat.problem2_3_exists_adjacentSingleGap_of_ieeeSingle_realOrderAdjacentNormalized_ordered` and `FloatingPointFormat.problem2_3_exists_adjacentSingleGap_of_ieeeSingle_realOrderAdjacentNormalized` prove that arbitrary finite IEEE-single normalized endpoints that are adjacent in the local real-order normalized vocabulary are represented by the same branch-family constructors. The `*_mem_iff` lemmas characterize the listed intervals exactly by strict scaled mantissa bounds, and the `problem2_3_ieeeDouble_*_between_iff_mem` classifiers prove positive and negative strict-between equivalences for the same-exponent, exponent-boundary, and subnormal-block branches. The finite-system no-extra theorems `FloatingPointFormat.problem2_3_ieeeDouble_finiteSystem_sameExponent_signed_between_exists_mem`, `FloatingPointFormat.problem2_3_ieeeDouble_finiteSystem_boundary_signed_between_exists_mem`, and `FloatingPointFormat.problem2_3_ieeeDouble_finiteSystem_subnormalBlock_signed_between_exists_mem` exclude zero/subnormal or wrong-binade cases and return listed mantissas for every finite IEEE-double value between signed adjacent IEEE-single endpoints in the corresponding branch. The branch-family formulation `FloatingPointFormat.Problem2_3IeeeSingleAdjacentGap`, `FloatingPointFormat.problem2_3_adjacentSingleGap_between_iff_mem`, `FloatingPointFormat.problem2_3_adjacentSingleGapDoubleValue_finiteSystem_of_mem`, and `FloatingPointFormat.problem2_3_adjacentSingleGap_finiteSystem_between_exists_mem` packages those signed branches under one count/classifier/finite/no-extra theorem surface.

Chapter 2 finite-underflow output classifiers: `FloatingPointFormat.finiteSystem_finiteUnderflowRange_iff_zero_or_subnormalSystem`, `FloatingPointFormat.finiteSystem_finiteUnderflowRange_ne_zero_iff_subnormalSystem`, `FloatingPointFormat.nearestRoundingToFinite_output_underflow_zero_or_subnormalSystem`, and `FloatingPointFormat.nearestRoundingToFinite_output_underflow_ne_zero_subnormalSystem`.

Chapter 2 relation-valued signed subnormal nearest grid: `FloatingPointFormat.minSubnormalMagnitude_mem_subnormalSystem_of_subnormalMantissa_one`, `FloatingPointFormat.two_mul_minSubnormalMagnitude_le_minNormalMagnitude_of_subnormalMantissa_one`, `FloatingPointFormat.nearestRoundingToFinite_minSubnormalMagnitude_of_half_le_of_le_three_halves`, `FloatingPointFormat.finiteSystem_neg`, `FloatingPointFormat.nearestRoundingToFinite_neg`, `FloatingPointFormat.nearestRoundingToFinite_neg_minSubnormalMagnitude_of_neg_three_halves_le_of_le_neg_half`, `FloatingPointFormat.nearestRoundingToFinite_subnormalValue_false_of_half_cell`, and `FloatingPointFormat.nearestRoundingToFinite_subnormalValue_true_of_half_cell`.

Chapter 2 relation-valued finite underflow existence and total arbitrary finite nearest choice: `FloatingPointFormat.minNormalMagnitude_eq_minNormalMantissa_mul_minSubnormalMagnitude`, `FloatingPointFormat.nearestRoundingToFinite_minNormalMagnitude_of_subnormal_boundary_half_le`, `FloatingPointFormat.nearestRoundingToFinite_neg_minNormalMagnitude_of_subnormal_boundary_half_le`, `FloatingPointFormat.exists_nat_half_cell_of_half_lt_of_lt_sub_half`, `FloatingPointFormat.exists_nearestRoundingToFinite_positive_subnormal_middle`, `FloatingPointFormat.exists_nearestRoundingToFinite_nonneg_finiteUnderflowRange`, `FloatingPointFormat.exists_nearestRoundingToFinite_nonpos_finiteUnderflowRange`, `FloatingPointFormat.exists_nearestRoundingToFinite_finiteUnderflowRange`, `FloatingPointFormat.exists_nearestRoundingToFinite`, `FloatingPointFormat.finiteNearestFl`, `FloatingPointFormat.finiteNearestFl_nearestRoundingToFinite`, `FloatingPointFormat.finiteNearestFl_output_not_finiteOverflowRange`, and `FloatingPointFormat.finiteNearestFl_output_abs_le_maxFiniteMagnitude`.  `finiteNearestFl` is arbitrary on ties; source-facing tie policies and IEEE exception behavior remain separate.

Chapter 2 source-facing finite round-away selector: `FloatingPointFormat.finiteUnderflowRoundAwayNonneg`, `FloatingPointFormat.finiteUnderflowRoundAwayNonneg_nearestRoundingToFinite`, `FloatingPointFormat.finiteUnderflowRoundAway`, `FloatingPointFormat.finiteUnderflowRoundAway_nearestRoundingToFinite`, `FloatingPointFormat.finiteRoundAway`, `FloatingPointFormat.finiteRoundAway_nearestRoundingToFinite`, `FloatingPointFormat.finiteRoundAway_output_not_finiteOverflowRange`, `FloatingPointFormat.finiteRoundAway_output_abs_le_maxFiniteMagnitude`, `FloatingPointFormat.finiteRoundAway_sourceRoundAwayEvidence_of_finiteNormalRange`, `FloatingPointFormat.finiteRoundAway_signedRelErrorWitness_lt_of_finiteNormalRange`, `FloatingPointFormat.finiteRoundAway_inverseRelErrorModel_of_finiteNormalRange`, and `FloatingPointFormat.finiteRoundAway_inverseRelErrorWitness_of_finiteNormalRange`.  This gives a source-facing round-away choice over underflow, finite-normal, and overflow ranges; directed modes and IEEE exception/flag behavior remain separate.

Chapter 2 local adjacent and finite-normal round-to-even selectors: `FloatingPointFormat.evenMantissa`, `FloatingPointFormat.nearestAdjacentRoundToEven`, `FloatingPointFormat.nearestAdjacentRoundToEven_eq_left_of_left_closer`, `FloatingPointFormat.nearestAdjacentRoundToEven_eq_right_of_right_closer`, `FloatingPointFormat.nearestAdjacentRoundToEven_eq_left_of_tie_even`, `FloatingPointFormat.nearestAdjacentRoundToEven_eq_right_of_tie_odd`, `FloatingPointFormat.nearestAdjacentRoundToEven_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between`, `FloatingPointFormat.nearestAdjacentRoundToEven_nearestRoundingToUnbounded_of_sameExponentAdjacentNormalized_ordered_between`, `FloatingPointFormat.adjacentRoundTowardNegative`, `FloatingPointFormat.adjacentRoundTowardPositive`, `FloatingPointFormat.adjacentRoundTowardZero`, `FloatingPointFormat.adjacentRoundTowardNegative_eq_right_of_eq_right`, `FloatingPointFormat.adjacentRoundTowardNegative_eq_left_of_ne_right`, `FloatingPointFormat.adjacentRoundTowardPositive_eq_left_of_eq_left`, `FloatingPointFormat.adjacentRoundTowardPositive_eq_right_of_ne_left`, `FloatingPointFormat.adjacentRoundTowardZero_eq_towardPositive_of_neg`, `FloatingPointFormat.adjacentRoundTowardZero_eq_towardNegative_of_nonneg`, `FloatingPointFormat.adjacentRoundTowardNegative_mem_unboundedNormalized`, `FloatingPointFormat.adjacentRoundTowardPositive_mem_unboundedNormalized`, `FloatingPointFormat.adjacentRoundTowardZero_mem_unboundedNormalized_of_nonneg_between`, `FloatingPointFormat.adjacentRoundTowardZero_mem_unboundedNormalized_of_nonpos_between`, `FloatingPointFormat.adjacentRoundTowardNegative_le_of_ordered_between`, `FloatingPointFormat.le_adjacentRoundTowardPositive_of_ordered_between`, `FloatingPointFormat.adjacentRoundTowardZero_nonneg_le_of_nonneg_between`, `FloatingPointFormat.adjacentRoundTowardZero_le_nonpos_of_nonpos_between`, `FloatingPointFormat.adjacentRoundTowardZero_abs_le_abs_of_nonneg_between`, `FloatingPointFormat.adjacentRoundTowardZero_abs_le_abs_of_nonpos_between`, `FloatingPointFormat.sourceRoundToEvenEvidence`, `FloatingPointFormat.sourceRoundToEvenEvidence_relErrorComputedDenom_le_unitRoundoff`, `FloatingPointFormat.exists_nearestAdjacentRoundToEven_signedRelErrorWitness_lt_positive`, `FloatingPointFormat.exists_nearestAdjacentRoundToEven_signedRelErrorWitness_lt_negative`, `FloatingPointFormat.exists_finiteNormalRoundToEven_signedRelErrorWitness_lt_finiteNormalRange`, `FloatingPointFormat.finiteNormalRoundToEven`, `FloatingPointFormat.finiteNormalRoundToEven_nearestRoundingToFinite`, `FloatingPointFormat.finiteNormalRoundToEven_signedRelErrorWitness_lt`, and `FloatingPointFormat.finiteNormalRoundToEven_inverseRelErrorWitness`.  This closes the local adjacent-bracket tie-to-even policy, adds the local adjacent-bracket directed choices toward negative, positive, and zero with exact endpoint preservation, representability, and one-sided/order facts, and closes the finite-normal source-facing round-to-even choice.  The total finite directed selector layer is now covered below; IEEE semantics remain separate.

Chapter 2 source round-to-even evidence uniqueness: `FloatingPointFormat.nearestAdjacentRoundToEven_eq_left_endpoint`, `FloatingPointFormat.nearestAdjacentRoundToEven_eq_right_endpoint`, `FloatingPointFormat.sourceRoundToEvenEvidence_eq_self_of_unboundedNormalizedSystem`, `FloatingPointFormat.sourceRoundToEvenEvidence_eq_nearest_of_realOrderAdjacent_between`, `FloatingPointFormat.sourceRoundToEvenEvidence_unique`, and `FloatingPointFormat.finiteNormalRoundToEven_eq_of_sourceRoundToEvenEvidence`.  This proves that source round-to-even evidence uniquely determines the finite-normal selector output, including exact representable inputs, endpoint brackets, strict-nearer branches, and half-tie parity branches.  The source-evidence sign-symmetry and finite-selector oddness wrappers used for Problem 2.7 are covered next.

Chapter 2 local and finite round-to-even sign-symmetry foundation: `FloatingPointFormat.evenMantissa_succ_iff_not_evenMantissa`, `FloatingPointFormat.evenMantissa_iff_not_evenMantissa_succ`, `FloatingPointFormat.evenMantissa_minNormalMantissa_of_even_beta`, `FloatingPointFormat.not_evenMantissa_maxNormalMantissa_of_even_beta`, `FloatingPointFormat.evenMantissa_minNormalMantissa_iff_not_evenMantissa_maxNormalMantissa_of_even_beta`, `FloatingPointFormat.evenMantissa_maxNormalMantissa_iff_not_evenMantissa_minNormalMantissa_of_even_beta`, `FloatingPointFormat.nearestAdjacentRoundToEven_neg_of_even_right_iff_not_even_left`, `FloatingPointFormat.realOrderAdjacentNormalized_neg_ordered`, `FloatingPointFormat.realOrderAdjacentNormalized_right_mantissa_parity`, `FloatingPointFormat.sourceRoundToEvenEvidence_neg`, `FloatingPointFormat.finiteNormalRoundToEven_neg`, `FloatingPointFormat.finiteRoundToEven_neg_of_finiteNormalRange`, and `FloatingPointFormat.finiteRoundToEven_neg`.  This proves local adjacent-bracket oddness, packages source-evidence sign symmetry, and closes total finite round-to-even selector oddness under the binary/IEEE-style assumptions that the base is even and `1 < t`.  Full IEEE special values, flags, traps, and signed-zero behavior remain separate.

Chapter 2 finite directed selector layer: `FloatingPointFormat.sourceRoundTowardNegativeEvidence`, `FloatingPointFormat.sourceRoundTowardPositiveEvidence`, `FloatingPointFormat.sourceRoundTowardZeroEvidence`, `FloatingPointFormat.finiteNormalRoundTowardNegative`, `FloatingPointFormat.finiteNormalRoundTowardPositive`, `FloatingPointFormat.finiteNormalRoundTowardZero`, `FloatingPointFormat.finiteUnderflowRoundTowardZero`, `FloatingPointFormat.finiteUnderflowRoundTowardPositive`, `FloatingPointFormat.finiteUnderflowRoundTowardNegative`, `FloatingPointFormat.finiteRoundTowardNegative`, `FloatingPointFormat.finiteRoundTowardPositive`, `FloatingPointFormat.finiteRoundTowardZero`, `FloatingPointFormat.finiteRoundTowardNegative_le_of_finiteUnderflowRange`, `FloatingPointFormat.le_finiteRoundTowardPositive_of_finiteUnderflowRange`, `FloatingPointFormat.finiteRoundTowardZero_abs_le_abs`, `FloatingPointFormat.finiteRoundToMode`, `FloatingPointFormat.finiteRoundToModeOp`, and `FloatingPointFormat.finiteRoundToModeSqrt`.  This lifts the local exact-endpoint directed selectors through finite-normal source evidence, adds subnormal-lattice underflow branches, uses finite saturation for overflow branches, and packages finite real-valued mode selectors for primitive operations and square root.  The IEEE mode wrappers now have a mode-aware underflow result predicate and dispatch finite underflow/no-flag primitive-operation and square-root branches through `finiteRoundToModeOp`/`finiteRoundToModeSqrt`; the all-mode flush-bound additive-underflow adapters now cover finite directed underflow at the `alpha` bound.  Remaining IEEE work is traps, signaling-NaN/payload behavior, broader special values, and concrete IEEE operation semantics.

Chapter 2 source-facing finite round-to-even selector: `FloatingPointFormat.finiteUnderflowRoundToEvenNonneg`, `FloatingPointFormat.finiteUnderflowRoundToEvenNonneg_nearestRoundingToFinite`, `FloatingPointFormat.finiteUnderflowRoundToEven`, `FloatingPointFormat.finiteUnderflowRoundToEven_nearestRoundingToFinite`, `FloatingPointFormat.finiteRoundToEven`, `FloatingPointFormat.finiteRoundToEven_nearestRoundingToFinite`, `FloatingPointFormat.finiteRoundToEven_output_not_finiteOverflowRange`, `FloatingPointFormat.finiteRoundToEven_output_abs_le_maxFiniteMagnitude`, `FloatingPointFormat.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange`, `FloatingPointFormat.finiteRoundToEven_signedRelErrorWitness_lt_of_finiteNormalRange`, `FloatingPointFormat.finiteRoundToEven_inverseRelErrorModel_of_finiteNormalRange`, `FloatingPointFormat.finiteRoundToEven_inverseRelErrorWitness_of_finiteNormalRange`, `FloatingPointFormat.nearestRoundingIn_eq_self_of_mem`, `FloatingPointFormat.nearestRoundingToFinite_eq_self_of_finiteSystem`, and `FloatingPointFormat.finiteRoundToEven_eq_self_of_finiteSystem`.  This gives a source-facing round-to-even choice over underflow, finite-normal, and overflow ranges and proves exact finite representable inputs are fixed; directed modes and IEEE exception/flag behavior remain separate.

Chapter 2 ordinary finite round-to-even operation bridge: `FloatingPointFormat.finiteRoundToEvenOp`, `FloatingPointFormat.finiteRoundToEvenOp_nearestRoundingToFinite`, `FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem`, `FloatingPointFormat.finiteRoundToEvenOp_add_zero_of_finiteSystem`, `FloatingPointFormat.finiteRoundToEvenOp_signedRelErrorWitness_lt_of_finiteNormalRange`, `FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange`, `FloatingPointFormat.ieeeRoundToNearestEvenOpResult_standardModel_lt_of_finiteNormalRange`, `FloatingPointFormat.ieeeRoundToNearestEvenOpValueResult_standardModel_lt_of_finiteNormalRange`, `FloatingPointFormat.finiteRoundToEvenOp_inverseRelErrorWitness_of_finiteNormalRange`, `FloatingPointFormat.ieeeRoundToNearestEvenOpResult_sub_eq_finiteNoFlags_of_fergusonCondition`, `FloatingPointFormat.ieeeRoundToNearestEvenOpResult_sub_noFlags_of_fergusonCondition`, `FloatingPointFormat.ieeeRoundToNearestEvenOpResult_sub_toReal?_of_fergusonCondition`, `FloatingPointFormat.finiteRoundToEvenSqrt`, `FloatingPointFormat.finiteRoundToModeSqrt`, `FloatingPointFormat.finiteRoundToModeSqrt_nearestEven`, `FloatingPointFormat.finiteRoundToEvenSqrt_nearestRoundingToFinite`, `FloatingPointFormat.finiteRoundToEvenSqrt_eq_exact_of_finiteSystem`, `FloatingPointFormat.finiteRoundToEvenSqrt_standardModel_lt_of_finiteNormalRange`, `FloatingPointFormat.ieeeRoundToNearestEvenSqrtResult_standardModel_lt_of_finiteNormalRange`, `FloatingPointFormat.ieeeRoundToNearestEvenSqrtValueResult_standardModel_lt_of_finiteNormalRange`, and `FloatingPointFormat.finiteRoundToEvenSqrt_inverseRelErrorWitness_of_finiteNormalRange`.  This derives Higham's strict standard-model equation for exact primitive operations and square root when the exact result is finite-normal, packages square-root rounding by mode, and proves exactness when the exact result is finite representable; the nearest/even IEEE finite-normal wrappers also expose no-flags plus the same strict `toReal?` standard-model value, including through the guarded `IeeeValue` primitive-operation dispatch for ordinary finite operands with a visible division guard and through the finite-input square-root value wrapper, and Ferguson-condition subtraction reaches the IEEE nearest/even finite/no-flags exact-value branch. Full IEEE operation semantics remain separate.

Chapter 2 IEEE-facing result vocabulary: `IeeeRoundingMode`, `IeeeExceptionFlag`, `IeeeValue`, `IeeeComparisonClass`, `IeeeValue.isSignedZero`, `IeeeValue.ieeeUnordered`, `IeeeValue.ieeeEq`, `IeeeValue.ieeeLt`, `IeeeValue.ieeeGt`, `IeeeValue.ieeeCompareClass`, `IeeeOperationResult`, `IeeeOperationResult.finiteNoFlags`, `IeeeOperationResult.valueNoFlags`, `ieeeInvalidOperationResult`, `ieeeInvalidOperationDefaultResult`, `ieeeDivisionByZeroInput`, `ieeeDivisionByZeroResult`, `ieeeDivisionByZeroDefaultResult`, `ieeeDivisionByZeroDefaultResult?`, `ieeeDivisionByZeroSignedValue`, `ieeeDivisionByZeroFiniteZeroDefaultValue`, `ieeeQuietNaNPropagationResult`, `ieeePrimitiveInvalidOperationInput`, `ieeePrimitiveInvalidOperationResult`, `ieeePrimitiveMulSignedZeroValue`, `ieeePrimitiveMulSignedZeroResult`, `ieeePrimitiveMulSignedZeroResult?`, `ieeePrimitiveSignedZeroOverFiniteValue`, `ieeePrimitiveSignedZeroOverFiniteResult`, `ieeePrimitiveAddSubSignedZeroResult`, `ieeePrimitiveSpecialValueResult`, `ieeeSqrtInvalidResult`, `ieeeSqrtInvalidDefaultResult`, `ieeeSqrtSpecialValueResult`, `ieeeSqrtSignedZeroResult`, `FloatingPointFormat.ieeeOverflowValue`, `FloatingPointFormat.ieeeOverflowResult`, `FloatingPointFormat.ieeeOverflowDefaultResult`, `FloatingPointFormat.ieeeUnderflowResult`, `FloatingPointFormat.ieeeUnderflowDefaultResult`, `FloatingPointFormat.ieeeUnderflowModeRoundingEvidence`, `FloatingPointFormat.ieeeUnderflowModeResult`, `FloatingPointFormat.ieeeOverflowDefaultResult_ieeeOverflowResult_of_finiteOverflowRange`, `FloatingPointFormat.ieeeUnderflowDefaultResult_ieeeUnderflowResult`, `FloatingPointFormat.ieeeUnderflowDefaultResult_ieeeUnderflowModeResult`, `FloatingPointFormat.finiteOverflowSaturationIeeeFiniteResult_not_ieeeOverflowResult`, `FloatingPointFormat.ieeeRoundToNearestEvenOpResult`, `FloatingPointFormat.ieeeRoundToModeOpResult`, `FloatingPointFormat.ieeeRoundTowardZeroOpResult`, `FloatingPointFormat.ieeeRoundTowardPositiveOpResult`, `FloatingPointFormat.ieeeRoundTowardNegativeOpResult`, `FloatingPointFormat.ieeeRoundToNearestEvenOpResult_ieeeOverflowResult_of_finiteOverflowRange`, `FloatingPointFormat.ieeeRoundToModeOpResult_ieeeOverflowResult_of_finiteOverflowRange`, `FloatingPointFormat.ieeeRoundToModeOpResult_ieeeUnderflowModeResult_of_finiteUnderflowRange`, `FloatingPointFormat.ieeeRoundToModeOpResult_ieeeUnderflowModeResult_and_flushAdditiveUnderflowModel`, `FloatingPointFormat.ieeeRoundToNearestEvenOpResult_ieeeUnderflowResult_of_finiteUnderflowRange`, `FloatingPointFormat.ieeeRoundToNearestEvenOpResult_standardModel_lt_of_finiteNormalRange`, `FloatingPointFormat.ieeeRoundToNearestEvenOpResult_sub_eq_finiteNoFlags_of_fergusonCondition`, `FloatingPointFormat.ieeeRoundToNearestEvenOpResult_sub_noFlags_of_fergusonCondition`, `FloatingPointFormat.ieeeRoundToNearestEvenOpResult_sub_toReal?_of_fergusonCondition`, `FloatingPointFormat.ieeeRoundToNearestEvenSqrtResult`, `FloatingPointFormat.ieeeRoundToModeSqrtResult`, `FloatingPointFormat.ieeeRoundTowardZeroSqrtResult`, `FloatingPointFormat.ieeeRoundTowardPositiveSqrtResult`, `FloatingPointFormat.ieeeRoundTowardNegativeSqrtResult`, `FloatingPointFormat.ieeeRoundToModeSqrtResult_ieeeOverflowResult_of_finiteOverflowRange`, `FloatingPointFormat.ieeeRoundToModeSqrtResult_ieeeUnderflowModeResult_of_finiteUnderflowRange`, `FloatingPointFormat.ieeeRoundToModeSqrtResult_ieeeUnderflowModeResult_and_flushAdditiveUnderflowModel`, `FloatingPointFormat.ieeeRoundToNearestEvenSqrtResult_ieeeSqrtInvalidResult_of_neg`, `FloatingPointFormat.ieeeRoundToNearestEvenSqrtResult_ieeeUnderflowResult_and_additiveUnderflowModel`, `FloatingPointFormat.ieeeRoundToNearestEvenSqrtResult_standardModel_lt_of_finiteNormalRange`, `FloatingPointFormat.ieeeRoundToNearestEvenSqrtValueResult`, and `FloatingPointFormat.ieeeRoundToModeSqrtValueResult`.  This starts the IEEE overflow/underflow/invalid-operation/division-by-zero/special-value semantic layer by making finite and non-finite flag-free source-facing results explicit, adding signed-zero values and comparison predicates for modeled NaN unordered/unequal behavior, signed-zero equality, predicate-level comparison classification, and the quiet/default four-way selector `IeeeValue.ieeeCompareClass`, adding quiet NaN propagation and primitive invalid-operation predicates for `0/0`, `0 * infinity`, `infinity * 0`, `infinity / infinity`, and indeterminate infinity addition/subtraction, adding no-flag signed-zero multiplication branches for signed-zero finite operands and now packaging that branch as an `Option` selector with exact source-case equations through the special-value, primitive-value, ordinary operation, and inexact-aware operation selectors, adding no-flag signed-zero-over-finite division branches and mode-independent signed-zero add/sub branches, adding flagged overflow, finite gradual-underflow, invalid-operation/NaN, and finite-nonzero-over-zero infinite-result predicates/constructors with signed `+0`/`-0` denominator infinity selection plus the ordinary modeled `finite 0` denominator default selector for positive and negative finite numerators, packaging those division-by-zero default results as an `Option` selector with a soundness theorem, proving finite saturation is not IEEE overflow semantics, adding nearest/even and mode-parameterized primitive-operation wrappers whose overflow branches use the IEEE rounding-mode table, dispatching mode-parameterized primitive-operation finite underflow/no-flag branches through `finiteRoundToModeOp`, exposing nearest/even finite-normal primitive-operation and square-root standard-model values through no-flags `toReal?` wrappers, adding a nearest/even finite/no-flags exact-value bridge for Ferguson-condition subtraction, adding mode-parameterized square-root wrappers whose finite branches use `finiteRoundToModeSqrt`, adding square-root non-finite branches for NaN, positive infinity, and negative infinity, proving square root preserves positive and negative zero with no flags, and lifting those square-root value branches to every rounding mode.  Full IEEE traps, signaling-NaN/payload behavior, executable primitive binary-operation value semantics beyond the guarded predicate layer, remaining special-value propagation, and comparison-instruction semantics beyond the quiet/default classifier remain open.

Chapter 2 square-root value selector update: `FloatingPointFormat.ieeeRoundToModeSqrtValueResult?`, `FloatingPointFormat.ieeeRoundToNearestEvenSqrtValueResult?`, `FloatingPointFormat.ieeeRoundToModeSqrtValueResult?_eq_some`, the branch selectors `FloatingPointFormat.ieeeRoundToModeSqrtValueResult?_finite`, `FloatingPointFormat.ieeeRoundToModeSqrtValueResult?_nan`, `FloatingPointFormat.ieeeRoundToModeSqrtValueResult?_posZero`, `FloatingPointFormat.ieeeRoundToModeSqrtValueResult?_negZero`, `FloatingPointFormat.ieeeRoundToModeSqrtValueResult?_posInf`, `FloatingPointFormat.ieeeRoundToModeSqrtValueResult?_negInf`, and the soundness lemmas `FloatingPointFormat.ieeeRoundToModeSqrtValueResult?_sound` and `FloatingPointFormat.ieeeRoundToNearestEvenSqrtValueResult?_sound` package the existing quiet/default square-root value wrapper as a concrete `Option` selector.  This selector is total only over the repository's modeled value wrapper; traps, signaling-NaN payloads, environment state, and complete hardware instruction semantics remain open.

Chapter 2 finite inexact IEEE branch: `ieeeInexactResult`, `ieeeInexactDefaultResult`, `ieeeInexactDefaultResult_ieeeInexactResult`, `ieeeInexactResult_not_finiteNoFlags`, `FloatingPointFormat.ieeeRoundToModeOpInexactAwareResult`, `FloatingPointFormat.ieeeRoundToModeOpInexactAwareResult_ieeeInexactResult_of_ne_of_not_finiteOverflowRange_of_not_finiteUnderflowRange`, `FloatingPointFormat.ieeeRoundToModeOpInexactAwareResult_eq_finiteNoFlags_of_eq_of_not_finiteOverflowRange_of_not_finiteUnderflowRange`, `FloatingPointFormat.ieeeRoundToModeOpInexactAwareResult_ieeeInexactResult_of_finiteNormalRange_of_ne`, `FloatingPointFormat.ieeeRoundToModeOpInexactAwareResult_eq_finiteNoFlags_of_finiteNormalRange_of_eq`, `FloatingPointFormat.ieeeRoundToModeOpInexactAwareValueResult`, `FloatingPointFormat.ieeeRoundToModeOpInexactAwareValueResult_divisionByZeroDefault?`, `FloatingPointFormat.ieeeRoundToModeOpInexactAwareValueResult_mulSignedZeroDefault?`, `FloatingPointFormat.ieeeRoundToModeOpInexactAwareValueResult?`, `FloatingPointFormat.ieeeRoundToModeOpInexactAwareValueResult?_sound`, `FloatingPointFormat.ieeeRoundToModeOpInexactAwareValueResult?_ieeeInexactResult_of_finiteNormalRange_of_ne`, and `FloatingPointFormat.ieeeRoundToModeOpInexactAwareValueResult?_finiteNoFlags_of_finiteNormalRange_of_eq`.  This records Table 2.2's ordinary finite inexact exception and lifts it through the guarded primitive value-result selector: if the selected rounded finite result differs from the exact real operation result, the result has the inexact flag; if it equals the exact result, the same wrapper takes the finite/no-flags branch.  The concrete division-by-zero, finite-over-infinity, and signed-zero multiplication default selectors are explicitly lifted through this inexact-aware dispatch so they remain special/flagged branches rather than finite real fallback paths.  Overflow, underflow, traps, signaling-NaN/payload behavior, and total executable IEEE operations remain separate.

Quiet-NaN selector update: `ieeeQuietNaNPropagationResult?`, `ieeeQuietNaNPropagationResult?_left_nan`, `ieeeQuietNaNPropagationResult?_right_nan`, `ieeeQuietNaNPropagationResult?_none_of_not_isNaN`, and `ieeeQuietNaNPropagationResult?_sound` package the modeled quiet/default primitive NaN propagation branch as a concrete `Option` selector. `ieeePrimitiveSpecialValueResult_quietNaNDefault?`, `ieeePrimitiveValueBranchResult_quietNaNDefault?`, `FloatingPointFormat.ieeeRoundToModeOpValueResult_quietNaNDefault?`, and `FloatingPointFormat.ieeeRoundToModeOpInexactAwareValueResult_quietNaNDefault?` lift the selected no-flag NaN result through the special-value, primitive-value, ordinary value-dispatch, and inexact-aware value-dispatch predicates.  The exact ordered-selector aliases `ieeePrimitiveSpecialValueResult?_left_nan`, `ieeePrimitiveValueBranchResult?_right_nan`, `FloatingPointFormat.ieeeRoundToModeOpValueResult?_left_nan`, and `FloatingPointFormat.ieeeRoundToModeOpInexactAwareValueResult?_right_nan` expose the left/right quiet-NaN cases through all four deterministic selector layers. Signaling NaNs, payload selection/propagation, traps, and language-specific NaN instruction behavior remain outside this modeled selector.

Invalid-operation selector update: `ieeePrimitiveInvalidOperationResult?`, its source-shape orientation theorems for `0/0`, `infinity/infinity`, `0*infinity`, `infinity*0`, opposite-signed infinity addition, and same-signed infinity subtraction, and `ieeePrimitiveInvalidOperationResult?_sound` package the modeled primitive invalid-operation branch as a concrete `Option` selector returning the default NaN result with the invalid-operation flag. `ieeePrimitiveSpecialValueResult_invalidOperationDefault?`, `ieeePrimitiveValueBranchResult_invalidOperationDefault?`, `FloatingPointFormat.ieeeRoundToModeOpValueResult_invalidOperationDefault?`, and `FloatingPointFormat.ieeeRoundToModeOpInexactAwareValueResult_invalidOperationDefault?` lift the selected flagged NaN result through the special-value, primitive-value, ordinary value-dispatch, and inexact-aware value-dispatch predicates. `ieeePrimitiveSpecialValueResult?_of_invalidOperationInput`, `ieeePrimitiveValueBranchResult?_of_invalidOperationInput`, `FloatingPointFormat.ieeeRoundToModeOpValueResult_of_invalidOperationInput`, and `FloatingPointFormat.ieeeRoundToModeOpInexactAwareValueResult_of_invalidOperationInput`, plus their concrete add/sub/mul/div source-case aliases, expose the same invalid-operation precedence through the ordered selectors and operation predicates. Traps, signaling-NaN behavior, payload selection/propagation, and total executable IEEE operations remain outside this selector.

Chapter 2 IEEE primitive special-value propagation: `IeeeValue.isPositiveNonzero`, `IeeeValue.isNegativeNonzero`, `IeeeValue.isNonnegativeSigned`, `IeeeValue.isNegativeSigned`, `IeeeValue.isSignedZero`, `ieeePrimitiveMulInfinityValue`, `ieeePrimitiveMulInfinityPropagationResult`, `ieeePrimitiveDivInfinityValue`, `ieeePrimitiveDivInfinityPropagationResult`, `ieeePrimitiveFiniteOverInfinityZeroValue`, `ieeePrimitiveFiniteOverInfinityResult`, `ieeePrimitiveMulSignedZeroValue`, `ieeePrimitiveMulSignedZeroResult`, `ieeePrimitiveMulSignedZeroResult?`, `ieeePrimitiveMulSignedZeroResult?_sound`, `ieeePrimitiveSignedZeroOverFiniteValue`, `ieeePrimitiveSignedZeroOverFiniteResult`, `ieeePrimitiveAddSubSignedZeroResult`, `ieeePrimitiveInfinityPropagationResult`, `ieeePrimitiveMulInfinityPropagationResult_posInf_of_positive_positive`, `ieeePrimitiveMulInfinityPropagationResult_posInf_of_negative_negative`, `ieeePrimitiveMulInfinityPropagationResult_negInf_of_positive_negative`, `ieeePrimitiveMulInfinityPropagationResult_negInf_of_negative_positive`, `ieeePrimitiveDivInfinityPropagationResult_posInf_of_positive_positive`, `ieeePrimitiveDivInfinityPropagationResult_negInf_of_negative_positive`, `ieeePrimitiveFiniteOverInfinityResult_posZero_of_nonnegative_positive`, `ieeePrimitiveFiniteOverInfinityResult_negZero_of_nonnegative_negative`, `ieeePrimitiveFiniteOverInfinityResult_posZero_posInf`, `ieeePrimitiveFiniteOverInfinityResult_posZero_negInf`, `ieeePrimitiveFiniteOverInfinityResult_negZero_posInf`, `ieeePrimitiveFiniteOverInfinityResult_negZero_negInf`, `ieeePrimitiveFiniteOverInfinityResult_finite_zero_posInf`, `ieeePrimitiveFiniteOverInfinityResult_finite_zero_negInf`, `ieeePrimitiveMulSignedZeroResult_posZero_posZero`, `ieeePrimitiveMulSignedZeroResult_posZero_negZero`, `ieeePrimitiveMulSignedZeroResult_negZero_posZero`, `ieeePrimitiveMulSignedZeroResult_negZero_negZero`, `ieeePrimitiveMulSignedZeroResult_posZero_of_posZero_finite_nonneg`, `ieeePrimitiveMulSignedZeroResult_negZero_of_posZero_finite_neg`, `ieeePrimitiveMulSignedZeroResult_posZero_of_finite_nonneg_posZero`, `ieeePrimitiveMulSignedZeroResult_negZero_of_finite_neg_posZero`, `ieeePrimitiveMulSignedZeroResult_negZero_of_negZero_finite_nonneg`, `ieeePrimitiveMulSignedZeroResult_posZero_of_negZero_finite_neg`, `ieeePrimitiveMulSignedZeroResult_negZero_of_finite_nonneg_negZero`, `ieeePrimitiveMulSignedZeroResult_posZero_of_finite_neg_negZero`, `ieeePrimitiveMulSignedZeroResult_noFlags`, `ieeePrimitiveSignedZeroOverFiniteResult_posZero_of_posZero_finite_pos`, `ieeePrimitiveSignedZeroOverFiniteResult_negZero_of_posZero_finite_neg`, `ieeePrimitiveSignedZeroOverFiniteResult_negZero_of_negZero_finite_pos`, `ieeePrimitiveSignedZeroOverFiniteResult_posZero_of_negZero_finite_neg`, `ieeePrimitiveSignedZeroOverFiniteResult_noFlags`, `ieeePrimitiveAddSubSignedZeroResult_add_posZero_posZero`, `ieeePrimitiveAddSubSignedZeroResult_add_negZero_negZero`, `ieeePrimitiveAddSubSignedZeroResult_sub_posZero_negZero`, `ieeePrimitiveAddSubSignedZeroResult_sub_negZero_posZero`, `ieeePrimitiveAddSubSignedZeroResult_noFlags`, `ieeePrimitiveInfinityPropagationResult_mul_posInf_posInf`, `ieeePrimitiveInfinityPropagationResult_mul_posInf_negInf`, `ieeePrimitiveInfinityPropagationResult_mul_negInf_posInf`, `ieeePrimitiveInfinityPropagationResult_mul_negInf_negInf`, `ieeePrimitiveInfinityPropagationResult_noFlags`, `ieeePrimitiveFiniteOverInfinityResult_noFlags`, `ieeePrimitiveSpecialValueResult_infinity`, `ieeePrimitiveSpecialValueResult_mulSignedZero`, `ieeePrimitiveSpecialValueResult_mulSignedZeroDefault?`, `ieeePrimitiveSpecialValueResult_signedZeroOverFinite`, `ieeePrimitiveSpecialValueResult_addSubSignedZero`, and `ieeePrimitiveSpecialValueResult_finiteOverInfinity`.  This closes the current predicate-layer no-flag add/sub infinity-infinity, finite-or-signed-zero mixed add/sub infinity, sign-selected multiplication infinity, signed-zero multiplication for finite operands in every explicit finite/signed-zero orientation, signed-zero divided by finite-nonzero signed-zero division, mode-independent same-signed zero addition and opposite-signed zero subtraction, infinite-numerator divided-by-finite-nonzero infinity, and finite-or-signed-zero divided-by-infinity signed-zero branches complementary to the invalid indeterminate cases; signed-zero multiplication is now also packaged as a concrete default selector with soundness into the special-value predicate.  Full executable IEEE operation semantics, traps, signaling-NaN/payload behavior, and remaining special-value branches remain open.

Signed-zero-over-finite division selector update: `ieeePrimitiveSignedZeroOverFiniteResult?`, its four signed-zero/finite-nonzero orientation theorems, finite-zero denominator `none` theorems, and `ieeePrimitiveSignedZeroOverFiniteResult?_sound` package the `signed zero / finite nonzero -> signed zero` branch as a concrete `Option` selector. `ieeePrimitiveSpecialValueResult_signedZeroOverFiniteDefault?`, `ieeePrimitiveValueBranchResult_signedZeroOverFiniteDefault?`, `FloatingPointFormat.ieeeRoundToModeOpValueResult_signedZeroOverFiniteDefault?`, and `FloatingPointFormat.ieeeRoundToModeOpInexactAwareValueResult_signedZeroOverFiniteDefault?` lift the selected result through the special-value, primitive-value, ordinary value-dispatch, and inexact-aware value-dispatch predicates. Exact source-case equations now expose the four positive/negative finite-denominator orientations through `ieeePrimitiveSpecialValueResult?`, `ieeePrimitiveValueBranchResult?`, `FloatingPointFormat.ieeeRoundToModeOpValueResult?`, and `FloatingPointFormat.ieeeRoundToModeOpInexactAwareValueResult?`, for example `..._div_posZero_finite_pos`, `..._div_posZero_finite_neg`, `..._div_negZero_finite_pos`, and `..._div_negZero_finite_neg`.

Mode-independent signed-zero add/sub selector update: `ieeePrimitiveAddSubSignedZeroResult?`, its four same-sign-add/opposite-sign-sub orientation theorems, four mode-sensitive zero-sum `none` theorems, and `ieeePrimitiveAddSubSignedZeroResult?_sound` package the branch as a concrete `Option` selector. `ieeePrimitiveSpecialValueResult_addSubSignedZeroDefault?`, `ieeePrimitiveValueBranchResult_addSubSignedZeroDefault?`, `FloatingPointFormat.ieeeRoundToModeOpValueResult_addSubSignedZeroDefault?`, and `FloatingPointFormat.ieeeRoundToModeOpInexactAwareValueResult_addSubSignedZeroDefault?` lift the selected result through the same dispatch layers; opposite-signed zero addition and same-signed zero subtraction remain in the rounding-mode-aware zero-sum branch.

Chapter 2 IEEE infinity source examples: `ieeePrimitiveMulInfinityPropagationResult_posInf_of_finite_pos_posInf`, `ieeePrimitiveMulInfinityPropagationResult_negInf_of_finite_neg_posInf`, `ieeePrimitiveMulInfinityPropagationResult_negInf_of_finite_pos_negInf`, `ieeePrimitiveMulInfinityPropagationResult_posInf_of_finite_neg_negInf`, `ieeePrimitiveMulInfinityPropagationResult_posInf_of_posInf_finite_pos`, `ieeePrimitiveMulInfinityPropagationResult_negInf_of_posInf_finite_neg`, `ieeePrimitiveMulInfinityPropagationResult_negInf_of_negInf_finite_pos`, `ieeePrimitiveMulInfinityPropagationResult_posInf_of_negInf_finite_neg`, `ieeePrimitiveFiniteOverInfinityResult_posZero_of_finite_nonneg_posInf`, `ieeePrimitiveFiniteOverInfinityResult_negZero_of_finite_nonneg_negInf`, `ieeePrimitiveFiniteOverInfinityResult_negZero_of_finite_neg_posInf`, and `ieeePrimitiveFiniteOverInfinityResult_posZero_of_finite_neg_negInf` expose the source examples `(-1) * infinity = -infinity` and `finite / infinity = 0` through sign-selected no-flag predicate constructors.  The ordinary `finite 0` payload still uses the local positive-zero default; full executable IEEE operations and traps remain outside this predicate layer.

Finite-over-infinity selector update: `ieeePrimitiveFiniteOverInfinityResult?`, its signed-zero and finite-numerator concrete orientation theorems, and `ieeePrimitiveFiniteOverInfinityResult?_sound` package the `finite-or-signed-zero / infinity -> signed zero` branch as a concrete `Option` selector. `ieeePrimitiveSpecialValueResult_finiteOverInfinityDefault?`, `ieeePrimitiveValueBranchResult_finiteOverInfinityDefault?`, `FloatingPointFormat.ieeeRoundToModeOpValueResult_finiteOverInfinityDefault?`, and `FloatingPointFormat.ieeeRoundToModeOpInexactAwareValueResult_finiteOverInfinityDefault?` lift the selected result through the special-value, primitive-value, ordinary value-dispatch, and inexact-aware value-dispatch predicates. Exact source-case equations now expose all selected signed-zero and ordinary-finite numerator orientations through `ieeePrimitiveSpecialValueResult?`, `ieeePrimitiveValueBranchResult?`, `FloatingPointFormat.ieeeRoundToModeOpValueResult?`, and `FloatingPointFormat.ieeeRoundToModeOpInexactAwareValueResult?`, including `..._div_posZero_posInf`, `..._div_negZero_of_posZero_negInf`, `..._div_finite_nonneg_posInf`, and `..._div_posZero_of_finite_neg_negInf`.

Infinity-propagation selector update: `ieeePrimitiveInfinityPropagationResult?` packages the quiet/default non-invalid add/sub infinity, multiplication-infinity, and infinite-numerator divided-by-finite-nonzero branches as a concrete `Option` selector.  The branch equations `ieeePrimitiveInfinityPropagationResult?_add_posInf_posInf`, `ieeePrimitiveInfinityPropagationResult?_add_negInf_negInf`, `ieeePrimitiveInfinityPropagationResult?_sub_posInf_negInf`, `ieeePrimitiveInfinityPropagationResult?_sub_negInf_posInf`, `ieeePrimitiveInfinityPropagationResult?_mul_posInf_posInf`, `ieeePrimitiveInfinityPropagationResult?_mul_posInf_negInf`, `ieeePrimitiveInfinityPropagationResult?_mul_negInf_posInf`, `ieeePrimitiveInfinityPropagationResult?_mul_negInf_negInf`, the finite-sign multiplication/division selector theorems, and the `none` theorems for opposite-signed infinity addition, same-signed infinity subtraction, zero-times-infinity, infinity over zero, and infinity over infinity make the selector surface explicit.  The finite-sign multiplication surface now includes the negative-infinity finite-operand orientations such as `ieeePrimitiveInfinityPropagationResult?_mul_negInf_finite_pos`, `ieeePrimitiveInfinityPropagationResult?_mul_posInf_of_negInf_finite_neg`, `ieeePrimitiveInfinityPropagationResult?_mul_finite_pos_negInf`, and `ieeePrimitiveInfinityPropagationResult?_mul_posInf_of_finite_neg_negInf`.  `ieeePrimitiveInfinityPropagationResult?_sound`, `ieeePrimitiveSpecialValueResult_infinityDefault?`, `ieeePrimitiveSpecialValueResult?_infinityDefault?`, `ieeePrimitiveValueBranchResult_infinityDefault?`, `ieeePrimitiveValueBranchResult?_infinityDefault?`, `FloatingPointFormat.ieeeRoundToModeOpValueResult_infinityDefault?`, `FloatingPointFormat.ieeeRoundToModeOpValueResult?_infinityDefault?`, `FloatingPointFormat.ieeeRoundToModeOpInexactAwareValueResult_infinityDefault?`, and `FloatingPointFormat.ieeeRoundToModeOpInexactAwareValueResult?_infinityDefault?` lift selected no-flag infinity results through the special-value, primitive-value, ordinary value-dispatch, and inexact-aware value-dispatch predicate and exact-selector layers. Invalid indeterminate infinity operations, zero times infinity, infinity over zero, and infinity over infinity remain outside this selector.

Chapter 2 IEEE mode-aware signed-zero add/sub zero sums: `IeeeRoundingMode.zeroSumSignedZeroValue`, `IeeeRoundingMode.zeroSumSignedZeroValue_nearestEven`, `IeeeRoundingMode.zeroSumSignedZeroValue_towardZero`, `IeeeRoundingMode.zeroSumSignedZeroValue_towardPositive`, `IeeeRoundingMode.zeroSumSignedZeroValue_towardNegative`, `ieeePrimitiveAddSubZeroSumResult`, `ieeePrimitiveAddSubZeroSumResult_add_posZero_negZero`, `ieeePrimitiveAddSubZeroSumResult_add_negZero_posZero`, `ieeePrimitiveAddSubZeroSumResult_sub_posZero_posZero`, `ieeePrimitiveAddSubZeroSumResult_sub_negZero_negZero`, `ieeePrimitiveAddSubZeroSumResult_noFlags`, `ieeePrimitiveAddSubZeroSumResult_left_nan`, `ieeePrimitiveAddSubZeroSumResult_right_nan`, `ieeePrimitiveAddSubZeroSumResult_finite_absurd`, `FloatingPointFormat.ieeeRoundToModeOpValueResult_addSubZeroSum`, `FloatingPointFormat.ieeeRoundToModeOpValueResult_add_posZero_negZero`, `FloatingPointFormat.ieeeRoundToModeOpValueResult_add_negZero_posZero`, `FloatingPointFormat.ieeeRoundToModeOpValueResult_sub_posZero_posZero`, and `FloatingPointFormat.ieeeRoundToModeOpValueResult_sub_negZero_negZero`.  This closes the no-flag exact-zero-sum signed-zero cases whose sign depends on the rounding mode: opposite-signed zero addition and same-signed zero subtraction return `-0` under round toward negative infinity and `+0` under nearest/even, toward zero, and toward positive.

Mode-aware signed-zero zero-sum selector update: `ieeePrimitiveAddSubZeroSumResult?`, its four mode-sensitive selected-orientation theorems, four mode-independent `none` theorems, and `ieeePrimitiveAddSubZeroSumResult?_sound` package the exact-zero-sum branch as a concrete `Option` selector. `FloatingPointFormat.ieeeRoundToModeOpValueResult_addSubZeroSumDefault?` and `FloatingPointFormat.ieeeRoundToModeOpInexactAwareValueResult_addSubZeroSumDefault?` lift the selected result through the ordinary and inexact-aware value-dispatch predicates; same-signed zero addition and opposite-signed zero subtraction remain in the mode-independent selector.

Chapter 2 IEEE mixed finite/signed-zero add/sub branches: `ieeePrimitiveAddSubFiniteSignedZeroResult`, `ieeePrimitiveAddSubFiniteSignedZeroResult_add_finite_signedZero`, `ieeePrimitiveAddSubFiniteSignedZeroResult_add_signedZero_finite`, `ieeePrimitiveAddSubFiniteSignedZeroResult_sub_finite_signedZero`, `ieeePrimitiveAddSubFiniteSignedZeroResult_sub_signedZero_finite`, `ieeePrimitiveAddSubFiniteSignedZeroResult?`, `ieeePrimitiveAddSubFiniteSignedZeroResult?_sound`, `ieeePrimitiveSpecialValueResult_addSubFiniteSignedZero`, `ieeePrimitiveSpecialValueResult_addSubFiniteSignedZeroDefault?`, `ieeePrimitiveValueBranchResult_addSubFiniteSignedZero`, `ieeePrimitiveValueBranchResult_addSubFiniteSignedZeroDefault?`, `FloatingPointFormat.ieeeRoundToModeOpValueResult_addSubFiniteSignedZeroDefault?`, and `FloatingPointFormat.ieeeRoundToModeOpInexactAwareValueResult_addSubFiniteSignedZeroDefault?`.  This closes the quiet/default predicate-layer cases where a finite nonzero payload is added to or subtracted from a signed zero, or a signed zero subtracts a finite nonzero payload, and now packages those cases as a concrete `Option` selector with soundness and ordinary/inexact-aware value-dispatch lifts.  Exact source-case selector equations now expose all eight concrete orientations through `ieeePrimitiveSpecialValueResult?`, `ieeePrimitiveValueBranchResult?`, `FloatingPointFormat.ieeeRoundToModeOpValueResult?`, and `FloatingPointFormat.ieeeRoundToModeOpInexactAwareValueResult?`, for example `..._add_finite_posZero`, `..._add_posZero_finite`, `..._sub_finite_negZero`, and `..._sub_negZero_finite`.  The ordinary modeled `finite 0` payload is intentionally excluded to avoid collapsing it with signed-zero result semantics.

Chapter 2 IEEE combined primitive branch selectors: `ieeePrimitiveSpecialValueResult?`, `ieeePrimitiveSpecialValueResult?_sound`, `ieeePrimitiveValueBranchResult?`, `ieeePrimitiveValueBranchResult?_sound`, `FloatingPointFormat.ieeeRoundToModeOpValueResult_primitiveValueBranchDefault?`, and `FloatingPointFormat.ieeeRoundToModeOpInexactAwareValueResult_primitiveValueBranchDefault?`.  These package the modeled quiet/default special-value branches and finite-nonzero-over-zero division-by-zero into ordered concrete selectors and lift any selected result through the ordinary and inexact-aware value-dispatch predicates.  The source-case equations now expose representative selected and precedence cases such as `ieeePrimitiveSpecialValueResult?_add_posInf_posInf`, `ieeePrimitiveValueBranchResult?_sub_posInf_negInf`, `ieeePrimitiveValueBranchResult?_mul_negInf_of_posInf_finite_neg`, `ieeePrimitiveValueBranchResult?_div_posInf_finite_pos`, `ieeePrimitiveValueBranchResult?_add_posInf_negInf`, and `ieeePrimitiveValueBranchResult?_div_posInf_posInf`, with ordinary and inexact-aware operation-predicate lifts such as `FloatingPointFormat.ieeeRoundToModeOpValueResult_add_posInf_posInf` and `FloatingPointFormat.ieeeRoundToModeOpInexactAwareValueResult_add_posInf_negInf`.  This is still predicate-level infrastructure, not total executable IEEE instruction semantics, traps, or signaling-NaN payload selection.

Chapter 2 IEEE primitive value dispatch: `ieeePrimitiveValueBranchResult`, `ieeePrimitiveValueBranchResult_special`, `ieeePrimitiveValueBranchResult_divisionByZero`, `ieeePrimitiveValueBranchResult_divisionByZeroDefault?`, `ieeePrimitiveValueBranchResult_mulSignedZeroDefault?`, `ieeePrimitiveValueBranchResult_signedZeroOverFinite`, `ieeePrimitiveValueBranchResult_addSubSignedZero`, `ieeePrimitiveValueBranchResult_addSubFiniteSignedZeroDefault?`, `FloatingPointFormat.ieeeRoundToModeOpValueResult`, `FloatingPointFormat.ieeeRoundToNearestEvenOpValueResult`, `FloatingPointFormat.ieeeRoundToModeOpValueResult_branch`, `FloatingPointFormat.ieeeRoundToModeOpValueResult_special`, `FloatingPointFormat.ieeeRoundToModeOpValueResult_divisionByZero`, `FloatingPointFormat.ieeeRoundToModeOpValueResult_divisionByZeroDefault?`, `FloatingPointFormat.ieeeRoundToModeOpValueResult_mulSignedZeroDefault?`, `FloatingPointFormat.ieeeRoundToModeOpValueResult_addSubFiniteSignedZeroDefault?`, `FloatingPointFormat.ieeeRoundToModeOpValueResult_finite_add`, `FloatingPointFormat.ieeeRoundToModeOpValueResult_finite_sub`, `FloatingPointFormat.ieeeRoundToModeOpValueResult_finite_mul`, `FloatingPointFormat.ieeeRoundToModeOpValueResult_finite_div_of_denominator_ne_zero`, `FloatingPointFormat.ieeeRoundToModeOpValueResult_finite_of_division_guard`, `FloatingPointFormat.ieeeRoundToNearestEvenOpValueResult_finite_of_division_guard`, `FloatingPointFormat.ieeeRoundToModeOpValueResult_noFlags_toReal?_of_finiteNormalRange`, and `FloatingPointFormat.ieeeRoundToNearestEvenOpValueResult_standardModel_lt_of_finiteNormalRange`.  This adds a guarded predicate-level dispatch that gives special-value, division-by-zero, and mode-aware exact-zero-sum signed-zero branches priority before the ordinary finite mode-aware operation wrapper, including signed-zero multiplication, signed-zero-over-finite division, and mode-independent signed-zero add/sub as special-value branches, lifts the concrete division-by-zero, signed-zero multiplication, and mixed finite/signed-zero default-result selectors through the primitive and operation value-dispatch predicates, and lifts the ordinary finite-normal/no-flags/value and nearest/even strict standard-model witnesses through that value-dispatch predicate for finite operands with an explicit nonzero-denominator guard for division; it does not model traps, signaling-NaN payloads, remaining special-value branches, or an executable hardware instruction.

Chapter 2 partial primitive value-result selector: `FloatingPointFormat.ieeeRoundToModeOpValueResult?`, `FloatingPointFormat.ieeeRoundToNearestEvenOpValueResult?`, `FloatingPointFormat.ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?`, `FloatingPointFormat.ieeeRoundToModeOpValueResult?_addSubZeroSumDefault?_of_no_branch`, `FloatingPointFormat.ieeeRoundToModeOpValueResult?_finite_of_no_value_branch`, `FloatingPointFormat.ieeeRoundToModeOpValueResult?_sound`, `FloatingPointFormat.ieeeRoundToModeOpValueResult?_finite_of_division_guard`, and `FloatingPointFormat.ieeeRoundToModeOpValueResult?_noFlags_toReal?_of_finiteNormalRange`.  This turns the current quiet/default branch layer into a deterministic partial `Option` selector: modeled special-value and division-by-zero branches are selected by the concrete `ieeePrimitiveValueBranchResult?` selector, mode-aware exact-zero-sum signed-zero branches are selected by `ieeePrimitiveAddSubZeroSumResult?` when no earlier branch applies, ordinary finite operands fall back to the mode-aware finite wrapper, and unmodeled non-finite cases remain `none` rather than being promoted to total IEEE hardware semantics.  Exact selector equations now expose representative signed-zero, special, invalid, and division-by-zero source cases such as `FloatingPointFormat.ieeeRoundToModeOpValueResult?_add_posZero_posZero`, `FloatingPointFormat.ieeeRoundToModeOpValueResult?_add_finite_posZero`, `FloatingPointFormat.ieeeRoundToModeOpValueResult?_add_posZero_finite`, `FloatingPointFormat.ieeeRoundToModeOpValueResult?_sub_negZero_finite`, `FloatingPointFormat.ieeeRoundToModeOpValueResult?_add_posZero_negZero`, `FloatingPointFormat.ieeeRoundToModeOpValueResult?_sub_posZero_posZero`, `FloatingPointFormat.ieeeRoundToModeOpValueResult?_div_posZero_posInf`, `FloatingPointFormat.ieeeRoundToModeOpValueResult?_div_finite_nonneg_posInf`, `FloatingPointFormat.ieeeRoundToModeOpValueResult?_add_posInf_negInf`, and `FloatingPointFormat.ieeeRoundToModeOpValueResult?_div_finite_pos_posZero`.

Chapter 2 no-guard digit model (2.6): `noGuardAddWitness`, `noGuardSubWitness`, `noGuardMulDivWitness`, `noGuardBasicOpWitness`, `NoGuardFPModel`, `noGuardAddWitness_error_eq`, `noGuardSubWitness_error_eq`, `noGuardMulDivWitness_error_eq`, `NoGuardFPModel.model_basicOp`, `NoGuardFPModel.model_add_error_eq`, `NoGuardFPModel.model_sub_error_eq`, `NoGuardFPModel.model_mul_signedRelErrorWitness`, and `NoGuardFPModel.model_div_signedRelErrorWitness`.  This formalizes Higham's weaker no-guard add/sub model with separate operand perturbations and strict mul/div relative-error model, and records the displayed three-bit binary example by `noGuardBinaryT3_exact_difference`, `noGuardBinaryT3_truncated_difference`, `noGuardBinaryT3_truncated_factor_two`, and `noGuardBinaryT3_truncated_relError_eq_one`.  The remaining guard-digit gap is a fully executable digit-level subtraction implementation, special-value/trap coverage, and a total full IEEE subtraction theorem beyond the finite-normal Ferguson nearest/even branch; it is not the source-facing finite-system Sterbenz exactness theorem.

Chapter 2 guard-digit exact-subtraction theorem surface:
`FloatingPointFormat.normalizedExponentRepresentation`,
`FloatingPointFormat.fergusonExponentCondition`,
`FloatingPointFormat.fergusonExponentConditionLe`,
`FloatingPointFormat.normalizedExponentRepresentation_sub_exponent_gap_le_one`,
`FloatingPointFormat.normalizedValue_sub_fergusonCondition_sign_eq`,
`FloatingPointFormat.fergusonExponentCondition_exponent_gap_le_one`,
`FloatingPointFormat.fergusonExponentCondition_same_sign_and_exponent_gap`,
`FloatingPointFormat.fergusonExponentCondition_same_sign_exponent_cases`,
`FloatingPointFormat.alignedSameExponentSubtractionValue`,
`FloatingPointFormat.sameExponentMantissaDiffInt`,
`FloatingPointFormat.sameExponentMantissaDiffInt_natAbs_lt_mantissaBound`,
`FloatingPointFormat.minNormalMantissa_mul_beta_eq_mantissaBound`,
`FloatingPointFormat.sameExponentRenormalizationWitness`,
`FloatingPointFormat.sameExponentSubnormalEndpointWitness`,
`FloatingPointFormat.sameExponent_shift_search`,
`FloatingPointFormat.scaledIntegerValue_finiteSystem_of_natAbs_lt_mantissaBound`,
`FloatingPointFormat.sameExponentFiniteDifferenceWitness`,
`FloatingPointFormat.sameExponentFiniteDifferenceWitness_of_normalizedMantissas`,
`FloatingPointFormat.normalizedValue_eq_subnormalValue_mul_beta_pow_of_subExponent_eq_emin`,
`FloatingPointFormat.guardDigitRoundedSameExponentSubtractionValue`,
`FloatingPointFormat.normalizedValue_sub_sameSign_sameExponent_eq_guardDigitRounded`,
`FloatingPointFormat.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_natAbs_eq_zero`,
`FloatingPointFormat.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_normalizedDiff`,
`FloatingPointFormat.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_beta_mul_normalizedDiff`,
`FloatingPointFormat.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_beta_pow_mul_normalizedDiff`,
`FloatingPointFormat.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_renormalizationWitness`,
`FloatingPointFormat.normalizedValue_sub_sameSign_sameExponent_finiteSystem_at_emin_of_natAbs_lt_minNormalMantissa`,
`FloatingPointFormat.normalizedValue_sub_sameSign_sameExponent_finiteSystem_at_shifted_emin_of_natAbs_mul_beta_pow_lt_minNormalMantissa`,
`FloatingPointFormat.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_subnormalEndpointWitness`,
`FloatingPointFormat.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_finiteDifferenceWitness`,
`FloatingPointFormat.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_normalizedMantissas`,
`FloatingPointFormat.sameExponentSubnormalEndpointWitness_of_emin_natAbs_lt_minNormalMantissa`,
`FloatingPointFormat.sameExponentFiniteDifferenceWitness_of_emin_natAbs_lt_minNormalMantissa`,
`FloatingPointFormat.guardAlignedMantissaDiff`,
`FloatingPointFormat.guardAlignedMantissaDiffInt`,
`FloatingPointFormat.guardAlignedMantissaDiffInt_cast`,
`FloatingPointFormat.alignedAdjacentExponentSubtractionValue`,
`FloatingPointFormat.alignedAdjacentExponentSubtractionValue_finiteSystem_of_natAbs_lt_mantissaBound`,
`FloatingPointFormat.normalizedValue_sub_sameSign_adjacentExponent_finiteSystem_of_natAbs_lt_mantissaBound`,
`FloatingPointFormat.guardAlignedMantissaDiff_abs_lt_minNormalMantissa_of_fergusonAdjacent`,
`FloatingPointFormat.guardAlignedMantissaDiffInt_abs_lt_minNormalMantissa_of_fergusonAdjacent`,
`FloatingPointFormat.guardAlignedMantissaDiffInt_natAbs_lt_minNormalMantissa_of_fergusonAdjacent`,
`FloatingPointFormat.guardAlignedMantissaDiffInt_pos_of_adjacentNormalizedMantissas`,
`FloatingPointFormat.guardAlignedMantissaDiffInt_natAbs_lt_mantissaBound_of_sterbenzAdjacent`,
`FloatingPointFormat.normalizedValue_sub_positive_adjacentExponent_finiteSystem_of_sterbenzAdjacent`,
`FloatingPointFormat.sterbenzRatioCondition_positive_normalized_exponent_gap_le_one`,
`FloatingPointFormat.normalizedValue_sub_positive_finiteSystem_of_sterbenzRatioCondition`,
`FloatingPointFormat.normalizedSystem_sub_finiteSystem_of_sterbenzRatioCondition`,
`FloatingPointFormat.subnormalValue_false_pos`,
`FloatingPointFormat.subnormalValue_true_neg`,
`FloatingPointFormat.subnormalValue_sub_sameSign_finiteSystem_of_subnormalMantissas`,
`FloatingPointFormat.subnormalSystem_sub_finiteSystem_of_sterbenzRatioCondition`,
`FloatingPointFormat.normalizedValue_sub_subnormalValue_positive_finiteSystem_of_sterbenzRatioCondition`,
`FloatingPointFormat.normalizedSystem_sub_subnormalSystem_finiteSystem_of_sterbenzRatioCondition`,
`FloatingPointFormat.subnormalSystem_sub_normalizedSystem_finiteSystem_of_sterbenzRatioCondition`,
`FloatingPointFormat.finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition`,
`FloatingPointFormat.finiteSystem_sub_finiteSystem_of_sterbenzRatioConditionLe`,
`FloatingPointFormat.guardDigitLeadingDigit`,
`FloatingPointFormat.guardDigitTailMantissa`,
`FloatingPointFormat.guardDigitRoundedCoeff`,
`FloatingPointFormat.guardDigitRoundedCoeff_eq_self_of_fergusonAdjacent`,
`FloatingPointFormat.guardDigitRoundedAdjacentExponentSubtractionValue`,
`FloatingPointFormat.normalizedValue_sub_sameSign_adjacentExponent_eq_guardDigitRounded_of_fergusonAdjacent`,
`FloatingPointFormat.guardAlignedMantissaDiffInt_natAbs_lt_minNormalMantissa_of_fergusonAdjacent_reversed`,
`FloatingPointFormat.normalizedValue_sub_sameSign_reversedAdjacentExponent_eq_neg_guardDigitRounded_of_fergusonAdjacent`,
`FloatingPointFormat.guardDigitRoundedBranchSubtractionValue`,
`FloatingPointFormat.guardDigitRoundedBranchSubtractionValue_eq_sub_of_ferguson`,
`FloatingPointFormat.guardDigitBranchSubtractionModel`,
`FloatingPointFormat.guardDigitBranchSubtractionModel_guardDigitSubtractionModel`,
`FloatingPointFormat.guardDigitBranchSubtractionModel_exact_of_fergusonCondition`,
`FloatingPointFormat.GuardDigitBranchSubtractionData`,
`FloatingPointFormat.GuardDigitBranchSubtractionData.branchValue_eq_sub`,
`FloatingPointFormat.guardDigitRoundedBranchSubtractionValue_finiteSystem_of_ferguson`,
`FloatingPointFormat.GuardDigitBranchSubtractionData.branchValue_finiteSystem`,
`FloatingPointFormat.guardDigitBranchSubtractionRoutine`,
`FloatingPointFormat.guardDigitBranchSubtractionRoutine_guardDigitSubtractionModel`,
`FloatingPointFormat.guardDigitBranchSubtractionRoutine_exact_of_fergusonCondition`,
`FloatingPointFormat.guardDigitBranchSubtractionRoutine_finiteSystem_of_data`,
`FloatingPointFormat.guardDigitBranchSubtractionRoutine_finiteSystem_of_fergusonCondition`,
`FloatingPointFormat.guardDigitSubtractionModel`,
`FloatingPointFormat.finiteRoundToEvenOp_sub_sameSign_sameExponent_eq_exact`,
`FloatingPointFormat.finiteRoundToEvenOp_sub_positive_adjacentExponent_eq_exact_of_sterbenzAdjacent`,
`FloatingPointFormat.finiteRoundToEvenOp_sub_positive_eq_exact_of_sterbenzRatioCondition`,
`FloatingPointFormat.finiteRoundToEvenOp_sub_normalizedSystem_eq_exact_of_sterbenzRatioCondition`,
`FloatingPointFormat.finiteRoundToEvenOp_sub_sameSign_subnormal_eq_exact`,
`FloatingPointFormat.finiteRoundToEvenOp_sub_subnormalSystem_eq_exact_of_sterbenzRatioCondition`,
`FloatingPointFormat.finiteRoundToEvenOp_sub_normalizedSystem_subnormalSystem_eq_exact_of_sterbenzRatioCondition`,
`FloatingPointFormat.finiteRoundToEvenOp_sub_subnormalSystem_normalizedSystem_eq_exact_of_sterbenzRatioCondition`,
`FloatingPointFormat.finiteRoundToEvenOp_sub_finiteSystem_eq_exact_of_sterbenzRatioCondition`,
`FloatingPointFormat.finiteRoundToEvenOp_sub_finiteSystem_eq_exact_of_sterbenzRatioConditionLe`,
`FloatingPointFormat.finiteRoundToEvenOp_sub_eq_exact_of_guardDigitBranchSubtractionData`,
`FloatingPointFormat.finiteRoundToEvenOp_sub_eq_exact_of_fergusonCondition`,
`FloatingPointFormat.finiteRoundToEvenOp_sub_eq_exact_of_fergusonConditionLe`,
`FloatingPointFormat.fergusonExponentCondition_sub_finiteNormalRange`,
`FloatingPointFormat.fergusonExponentConditionLe_sub_finiteNormalRange`,
`FloatingPointFormat.ieeeRoundToNearestEvenOpResult_sub_eq_finiteNoFlags_of_fergusonCondition`,
`FloatingPointFormat.ieeeRoundToNearestEvenOpResult_sub_noFlags_of_fergusonCondition`,
`FloatingPointFormat.ieeeRoundToNearestEvenOpResult_sub_toReal?_of_fergusonCondition`,
`FloatingPointFormat.ieeeRoundToNearestEvenOpResult_sub_eq_finiteNoFlags_of_fergusonConditionLe`,
`FloatingPointFormat.ieeeRoundToNearestEvenOpResult_sub_noFlags_of_fergusonConditionLe`,
`FloatingPointFormat.ieeeRoundToNearestEvenOpResult_sub_toReal?_of_fergusonConditionLe`,
`FloatingPointFormat.sterbenzRatioCondition`,
`FloatingPointFormat.sterbenzRatioConditionLe`,
`FloatingPointFormat.sterbenzRatioCondition_symm`,
`FloatingPointFormat.sterbenzRatioCondition_abs_sub_lt_min`,
`FloatingPointFormat.decimalSingleDigitFormat_sterbenzRatio_not_ferguson`,
`FloatingPointFormat.sterbenzFergusonBridgeCondition`,
`FloatingPointFormat.guardDigitSubtractionModel_exact_of_fergusonCondition`,
and `FloatingPointFormat.guardDigitSubtractionModel_exact_of_sterbenzBridge`.
This names Higham Theorem 2.4's exponent-side condition, proves the source
proof's exponent-gap, same-sign, and exact exponent-case reductions, formalizes
the raw aligned same-exponent and one-exponent-shift subtraction identities,
proves same-exponent mantissa subtraction has at most `t` digits and is
unchanged by the modeled t-digit rounding coefficient, proves the same-exponent
exact difference is finite normalized when the integer mantissa difference is
already normalized, proves the one-base-shift and arbitrary finite radix-power
shift same-exponent exact differences are finite normalized when the shifted
integer difference is normalized and the shifted exponent is in range, proves
the same-exponent exact difference is finite at `emin` when that integer
difference is below the normalized leading-digit threshold, and proves the
shifted-`emin` subnormal endpoint when a finite radix-power shift lands at
`emin` below the normalized leading-digit threshold.  These branches are now
packaged by `sameExponentFiniteDifferenceWitness`, whose finite-system wrapper
covers exact zero, a normalized renormalization shift, and a shifted `emin`
subnormal endpoint.  The selector is now derived from same-exponent normalized
operand mantissas and an in-range exponent, giving a source-facing finite-system
theorem for same-exponent exact subtraction. It proves the
guard-aligned mantissa coefficient, including its integer `beta*mHigh - mLow`
form, is below the normalized leading-digit threshold under both adjacent
orientations, proves the direct Sterbenz adjacent-exponent coefficient is
positive and below the `t`-digit mantissa bound under the ratio condition,
uses a generic bounded-integer finite-system adapter to turn that coefficient
bound into finite representability for the positive adjacent-exponent Sterbenz
branch, and connects that branch to exact concrete finite round-to-even
subtraction.  The ratio condition is also proved symmetric and strong enough
to force a one-exponent gap for positive normalized operands; combining that
gap with the same-exponent and both adjacent-exponent branches closes positive
normalized Sterbenz finite representability and exact concrete finite
round-to-even subtraction, and source-shaped wrappers now lift this to
`normalizedSystem` operands.  The same subnormal lattice is also closed for
same-sign subnormal subtraction, and the Sterbenz ratio condition forces
subnormal-system operands into the positive same-sign branch, giving exact
concrete finite round-to-even subtraction for all-subnormal Sterbenz operands.
The mixed normal/subnormal branch is closed by rewriting the normalized operand
on the subnormal lattice and bounding its exact integer difference coefficient
from the Sterbenz ratio condition; the finite-system all-case wrapper now gives
exact concrete finite round-to-even subtraction for all finite Sterbenz
operands, including the printed inclusive endpoint condition
`y/2 <= x <= 2*y`.  It formalizes the proof sentence that the leading digit `z1` of the
`t+1` guard word is zero with the trailing `t`-digit tail unchanged, proves that
dropping that zero guard digit and reattaching the sign leaves the
adjacent-exponent subtraction value exact, packages the
same-exponent/high-minus-low/low-minus-high branch cases into
`guardDigitBranchSubtractionModel`, provides a noncomputable evidence-selecting
`guardDigitBranchSubtractionRoutine` that satisfies `guardDigitSubtractionModel`
under Ferguson's condition, proves the branch-selected value is finite with the
same-exponent branch discharged by the derived finite-difference selector, and
connects the same-exponent and Ferguson-data cases to exact concrete finite
round-to-even subtraction, and specializes the IEEE nearest/even primitive-operation
wrapper to prove a finite/no-flags exact value for Ferguson-condition subtraction,
including the printed inclusive exponent condition
`e(x-y) <= min(e(x),e(y))`.
It also records a one-digit decimal counterexample
showing Sterbenz's ratio condition does not imply Ferguson's exponent condition
in general bases.  A fully executable digit-level subtraction implementation, special-value/trap coverage,
and a total full IEEE subtraction theorem beyond the finite-normal Ferguson
nearest/even branch remain open.

Chapter 2 Kahan parenthesized Heron formula (2.7): `heronSemiperimeter`,
`heronRadicand`, `heronArea`, `kahanHeronRadicand`, `kahanHeronArea`,
`finiteKahanHeronAB`, `finiteKahanHeronBC`, `finiteKahanHeronBplusC`,
`finiteKahanHeronFactor1`, `finiteKahanHeronFactor2`,
`finiteKahanHeronFactor3`, `finiteKahanHeronFactor4`,
`finiteKahanHeronProduct12`, `finiteKahanHeronProduct123`,
`finiteKahanHeronRadicand`, `finiteKahanHeronSqrt`, `finiteKahanHeronArea`,
`kahanHeronTraceStandardModel`, `kahanHeronExpandedRadicand`,
`kahanHeronBplusCRelativeDistortion`,
`kahanHeronBminusCRelativeDistortion`,
`kahanHeronRadicandLocalFactorProduct`, `kahanHeronRadicandLocalErrors`,
`finiteFormatUnitRoundoffModel`,
`kahanOrderedTriangleSides`,
`kahanHeronRadicand_eq_sixteen_mul_heronRadicand`,
`heronRadicand_pos_of_kahanOrderedTriangleSides`,
`kahanHeronRadicand_pos_of_kahanOrderedTriangleSides`,
`kahanHeronFactor_a_add_b_add_c_pos`, `kahanHeronFactor_b_sub_c_pos`,
`kahanHeronFactor_b_add_c_pos`, `kahanHeronFactor_c_sub_a_sub_b_pos`,
`kahanHeronFactor_c_add_a_sub_b_pos`,
`kahanHeronFactor_a_add_b_sub_c_pos`,
`kahanHeronExactFactors_pos_of_kahanOrderedTriangleSides`,
`kahanHeronRatio_b_add_c_abs_le_one`,
`kahanHeronRatio_b_sub_c_abs_le_one`,
`kahanHeronScaled_b_add_c_delta_abs_le_unitRoundoff`,
`kahanHeronScaled_b_sub_c_delta_abs_le_unitRoundoff`,
`kahanHeronArea_sq_eq_heronRadicand_of_kahanOrderedTriangleSides`,
`kahanOrderedTriangleSides_sterbenzRatioCondition_a_b`, and
`finiteRoundToEvenOp_sub_a_b_eq_exact_of_kahanOrderedTriangleSides`,
`finiteKahanHeronAB_eq_exact_of_kahanOrderedTriangleSides`, and the
`finiteKahanHeron*_standardModel_lt_of_finiteNormalRange` operation witnesses,
including `finiteKahanHeronTrace_standardModel_lt_of_finiteNormalRange`,
`kahanHeronTraceStandardModel_radicand_eq_expanded`, and
`kahanHeronTraceStandardModel_area_eq_expanded`,
`kahanHeronExpandedRadicand_eq_exact_mul_local_factors`,
`kahanHeronRadicandLocalErrors_abs_le_unitRoundoff`,
`kahanHeronTraceStandardModel_radicand_rel_error_le_gamma9`,
`kahanHeronTraceStandardModel_area_eq_gamma9_radicand`, and
`kahanHeronTraceStandardModel_area_eq_kahanArea_mul_sqrt_gamma9`,
`kahanHeronTraceStandardModel_area_relError_le_gamma9_unitRoundoff`, and
`finiteKahanHeronArea_relError_le_gamma9_unitRoundoff_of_finiteNormalRange`.
This records the exact algebra behind Kahan's parenthesized formula, names the finite round-to-even
operation trace through the product, square-root, and final division stages,
proves the parenthesized product is `16` times Heron's radicand, proves the
positive ordered-triangle squared-area identity and the positivity of all four
exact Kahan factors, connects the first inner subtraction `a-b` to exact finite
round-to-even subtraction via Sterbenz, gives strict standard-model witnesses
for every remaining rounded trace operation under the explicit
finite-normal-range hypotheses, packages them into one trace certificate with
exact expanded radicand and area equations, factors the expanded radicand into
the exact Kahan radicand times nine local relative-error factors, and aggregates
those factors into a `gamma 9` radicand relative-error theorem.  Under the
standard `gammaValid` guard for `18`, the area trace is also factored as exact
Kahan area times `sqrt (1 + theta)` and the two remaining local factors, and
the direct finite-normal-range theorem proves the closed relative-error bound
`(1 + gamma 9) * (1 + u)^2 - 1` for the modeled no-underflow trace.

Chapter 2 logarithmic leading-digit distribution (§2.5):
`leadingDigitOfIndex`, `logarithmicLeadingDigitMass`,
`logarithmicLeadingDigitMass_eq_log_div`,
`logarithmicLeadingDigitMass_eq_log_one_add_inv`,
`logarithmicIntervalMass`, `logarithmicIntervalMass_mul_base_pow`,
`logarithmicIntervalMass_mul_base_zpow`,
`logarithmicLeadingDigitMass_scaled_bin`,
`logarithmicLeadingDigitMass_scaled_bin_zpow`,
`logarithmicLeadingDigitMass_nonneg`,
`logarithmicLeadingDigitMass_succ_lt`,
`sum_logarithmicLeadingDigitMass_eq_one`,
`logarithmicLeadingDigitProbability`,
`logarithmicLeadingDigitProbability_prob_eq_log_div`,
`logarithmicLeadingDigitProbability_prob_eq_log_one_add_inv`,
`decimalLogarithmicLeadingDigitProbability_prob_eq`,
`decimalLogarithmicLeadingDigitProbability_prob_eq_log_one_add_inv`,
`decimalLogarithmicLeadingDigitProbability_first_gt_last`, and
`decimalLogarithmicLeadingDigitProbability_nonuniform`.  This records Higham's
displayed logarithmic law as a finite probability distribution on leading
digits `1, ..., beta-1`: each digit has mass
`log_beta ((n+1)/n) = log_beta (1+1/n)`, the masses
are nonnegative for `beta > 1`, the total mass telescopes to one, the masses
strictly decrease with the digit, decimal digit `1` has strictly greater mass
than decimal digit `9`, and natural/integer base-power rescaling leaves
logarithmic bin mass unchanged.  Brent's base-optimality
theorem, product-convergence explanations, and
`q^k` equidistribution remain open theorem targets; empirical table claims are
optional experiment/data artifacts unless a fully specified computation is
supplied.

Chapter 2 statistical rounding-error model (§2.6):
`statisticalRoundingErrorSum`, `StatisticalRoundingErrorModel`,
`StatisticalRoundingErrorModel.expectation_sum_eq_zero`,
`StatisticalRoundingErrorModel.expectation_sum_sq_eq_sum_second_moments`,
`StatisticalRoundingErrorModel.expectation_sum_sq_le_card_mul_unit_sq`, and
`StatisticalRoundingErrorModel.rms_sum_le_sqrt_card_mul_unit`.  This records
the finite second-moment core of Higham's `sqrt n` rule of thumb: under visible
zero-mean, pairwise-uncorrelated, per-step second-moment `<= u^2` assumptions,
the RMS accumulated error is at most `sqrt n * u`.  Concrete random-rounding
schemes, CLT/asymptotic normality, PRECISE/CESTAC models, and
logarithmic-mantissa rounding-error distributions remain open or descriptive.

Chapter 2 alternative number systems (§2.7):
`levelIndexForward`, `levelIndexBackward`, `levelIndexBackward_forward`,
`LevelIndexCode`, `LevelIndexCode.index`, `LevelIndexCode.value`,
`LevelIndexCode.reciprocalValue`,
`LevelIndexCode.backward_value_eq_frac`, and
`LevelIndexCode.reciprocalValue_mul_value_of_pos_level`.  This formalizes the
level-index arithmetic representation described in the text: a code stores a
level `l` and a fractional index `f in [0,1]`, decodes the positive-side value
by applying `exp` `l` times to `f`, recovers `f` by applying `log` `l` times,
and represents the reciprocal side by inverting the positive-side value.  The
claims about relative cost, word-length range, controversy, and other proposed
alternative systems remain descriptive.

Chapter 2 accuracy-test baselines (§2.8):
`unitRoundoffProbeExact`, `unitRoundoffProbeExact_eq_zero`,
`codySineTestExact`, `codySineReducedArgument`,
`codySineDisplayedTableMagnitude17`, `codySineDisplayedTableDecimal17`,
`codySineTestExact_eq_neg_sin_reducedArgument`,
`codySineTestExact_neg`, `codySineTestExact_abs_lt_one_hundredth`,
`sineTaylorOdd5`, `sineTaylorOdd5_eq`, `sineTaylorOdd5_abs_error_le_next`,
`codySineReducedArgument_sineTaylorOdd5_abs_error_lt_one_e20`,
`codySineTestExact_sineTaylorOdd5_abs_error_lt_one_e20`,
`codySineTaylorOdd5_displayedMagnitude_abs_error_lt_41e21`,
`codySineTestExact_displayedTableDecimal17_abs_error_lt_half_last_place`,
`codyPowerTestExact`, `codyPowerExpLogPath`,
`codyPowerDisplayedDecimal21`, `codyPowerDisplayedTableDecimal17`,
`codyPowerExpLogPath_eq_exact`,
`codyPowerTestExact_displayedDecimal21_abs_error_lt_half_last_place`,
`codyPowerTestExact_displayedTableDecimal17_abs_error_lt_half_last_place`,
`exp_absolute_error_relative_error_eq`,
`exp_absolute_error_relative_error_abs_lt_101_mul_abs`,
`karpinskiGuardDigitProbeA`, `karpinskiGuardDigitProbeB`,
`karpinskiGuardDigitFiniteProbeA`, `karpinskiGuardDigitFiniteProbeB`,
`karpinskiGuardDigitProbes_equal`, and
`FloatingPointFormat.decimalOneDigitThreeExponent_karpinskiProbes_equal`.  This records the exact real-arithmetic
baselines behind the Table 2.3 unit-roundoff probe, Cody's sine and
exponentiation tests, the exact argument-reduction identity
`sin(22) = -sin(22-7*pi)`, the proof that the reduced argument lies between
`0` and `0.01`, the resulting negative sign and coarse `|sin(22)| < 0.01`
bound, the five-term odd Taylor-polynomial remainder bound
`|sin(22-7*pi) - sineTaylorOdd5(22-7*pi)| < 10^-20` and its translated
`sin(22)` form, the rational interval proof that the Table 2.4 exact-row
decimal for `sin(22)` is within half of the last displayed place, the exact
equality of `2.5^125` with
`exp(125*log(2.5))`, the certified half-last-place intervals for the displayed
21-significant-digit decimal value of `2.5^125` and the shorter Table 2.5 exact
row, the source sensitivity identity saying an absolute error in `w` produces
relative error `exp(deltaW)-1` in `exp(w)`, the small-error bound that this
relative error is below `1.01*|deltaW|` when `|deltaW| < 0.01`, and the exact
equality of the two Karpinski guard-digit probes.  It also records a concrete
one-digit decimal finite round-to-even trace in which both Karpinski operation
paths compute `-0.1`.  Historical machine outputs, diagnostic software behavior,
and full guard-digit test-harness semantics remain open.

Chapter 2 fused multiply-add note (§2.6 and Problem 2.26):
`fusedMultiplyAddExact`, `FloatingPointFormat.finiteRoundToEvenFMA`,
`FloatingPointFormat.finiteRoundToModeFMA`,
`FloatingPointFormat.finiteRoundToEvenFMA_eq_round_exact`,
`FloatingPointFormat.finiteRoundToEvenFMA_eq_exact_of_finiteSystem`,
`FloatingPointFormat.finiteRoundToEvenFMA_standardModel_lt_of_finiteNormalRange`,
`FloatingPointFormat.finiteRoundToEvenFMA_inverseRelErrorWitness_of_finiteNormalRange`,
`FloatingPointFormat.finiteRoundToEvenFMA_product_correction_add_eq_product_of_finiteSystem`,
and `FloatingPointFormat.finiteRoundToEvenFMA_product_expansion_with_rounded_product`.
This formalizes the finite real-valued single-rounding surface of an FMA:
the exact quantity is `x*y+z`, and the finite wrapper rounds that value once at
the end.  It also closes the source-facing two-term product decomposition:
if the FMA correction `x*y-a` is representable, then `a+flFMA(x,y,-a)=x*y`,
including the wrapper where `a=fl(x*y)`.  Full IEEE FMA semantics with flags, signed zeros, infinities, NaNs,
traps, payloads, and hardware-specific details remain open.

Chapter 2 finite-format counts (Problem 2.1):
`FloatingPointFormat.normalizedExponentParameterCount`,
`FloatingPointFormat.normalizedMantissaParameterCount`,
`FloatingPointFormat.subnormalMantissaParameterCount`,
`FloatingPointFormat.normalizedNumberParameterCount`,
`FloatingPointFormat.subnormalNumberParameterCount`,
`FloatingPointFormat.normalizedNumberParameterCount_eq_problem2_1_formula`,
`FloatingPointFormat.subnormalNumberParameterCount_eq_problem2_1_formula`,
`FloatingPointFormat.subnormalValue_eq_iff_sign_mantissa`,
`FloatingPointFormat.problem2_1_ieeeSingle_normalizedNumberParameterCount`,
`FloatingPointFormat.problem2_1_ieeeSingle_subnormalNumberParameterCount`,
`FloatingPointFormat.problem2_1_ieeeDouble_normalizedNumberParameterCount`,
and `FloatingPointFormat.problem2_1_ieeeDouble_subnormalNumberParameterCount`.
This closes Problem 2.1 for the repository's inclusive finite-format model:
the signed nonzero normalized count is
`2 * (emax - emin + 1) * (beta^t - beta^(t-1))`, the signed nonzero
subnormal count is `2 * (beta^(t-1) - 1)`, IEEE single gives
`4,261,412,864` normalized and `16,777,214` subnormal values, and IEEE double
gives `18,428,729,675,200,069,632` normalized and
`9,007,199,254,740,990` subnormal values.  Full IEEE encodings, special
values, signed zeros, infinities, NaNs, flags, and traps remain outside this
finite-format count.

Chapter 2 adjacent-spacing proof (Problem 2.2 / Lemma 2.1):
`FloatingPointFormat.problem2_2_lemma2_1_spacing_bounds_left`,
`FloatingPointFormat.problem2_2_lemma2_1_spacing_bounds_right`, and
`FloatingPointFormat.problem2_2_lemma2_1_spacing_bounds`.  These expose the
exercise-level proof of Lemma 2.1 from the repository's real-order normalized
adjacency theorem: if `x` and `y` are adjacent normalized values, then the
spacing is between `beta^(-1) * eps_M * |x|` and `eps_M * |x|`, and likewise
with `|y|` as the reference endpoint.  This is a normalized finite-format
spacing theorem; subnormal, zero, and full IEEE special-value behavior are
tracked separately.

Chapter 2 inverse relative-error proof (Problem 2.4 / Theorem 2.3):
`FloatingPointFormat.problem2_4_theorem2_3_nearest_finite`,
`FloatingPointFormat.problem2_4_theorem2_3_finiteNormalFl`, and
`FloatingPointFormat.problem2_4_theorem2_3_finiteRoundToEven`.  These expose
the exercise-level proof of Theorem 2.3 over the finite-normal range: a nearest
finite rounded value, the source-style finite-normal choice, and the total
finite round-to-even selector all admit `fl(x) = x / (1 + delta)` with
`|delta| <= u` and `1 + delta != 0`.  This remains a finite-normal
finite-format theorem, not a full IEEE operation theorem with exceptions,
special values, flags, or traps.

Chapter 2 binary `0.1` and IEEE-single rounding error (Problem 2.5):
`FloatingPointFormat.problem2_5_binaryOneTenthTerm`,
`FloatingPointFormat.problem2_5_binaryOneTenth_hasSum`,
`FloatingPointFormat.problem2_5_binaryOneTenth_tsum`,
`FloatingPointFormat.problem2_5_ieeeSingle_roundToEven_oneTenth`, and
`FloatingPointFormat.problem2_5_ieeeSingle_oneTenth_relative_error`.  These
prove the repeating binary expansion as a geometric series summing to `1/10`,
prove that finite IEEE-single round-to-even maps `0.1` to
`13421773 * 2^-27`, and prove the displayed relative error
`(x - xhat) / x = -(1/4) * u` with `u = 2^-24`.  Decimal input conversion,
parser behavior, flags, and full IEEE result semantics remain separate.

Chapter 2 finite exercise facts (Problem 2.7):
`FloatingPointFormat.finiteRoundToEvenOp_add_comm`,
`FloatingPointFormat.finiteRoundToEvenOp_mul_comm`,
`FloatingPointFormat.problem2_7_statement2_sub_sign_symmetry_of_exact_finiteSystem`,
`FloatingPointFormat.problem2_7_statement2_sub_sign_symmetry_of_not_finiteNormalRange`,
`FloatingPointFormat.problem2_7_statement2_sub_sign_symmetry`,
`FloatingPointFormat.finiteRoundToEvenOp_add_self_eq_mul_two`,
`FloatingPointFormat.finiteRoundToEvenOp_half_mul_eq_div_two`,
`FloatingPointFormat.problem2_7_statement5_add_associativity_false`, and
`FloatingPointFormat.problem2_7_statement6_midpoint_strict_between_false`.
These close the ordinary finite round-to-even versions of Problem 2.7
statements 1, 3, and 4, close statement 2 for the total finite round-to-even
selector under even radix and `1 < t`, and give finite counterexamples to
statements 5 and 6.  The full IEEE-with-exceptions classification remains
open.

Chapter 2 decimal midpoint counterexample (Problem 2.8):
`FloatingPointFormat.decimalOneDigitTwoExponentFormat_finiteSystem_one`,
`FloatingPointFormat.decimalOneDigitTwoExponentFormat_finiteSystem_two`,
`FloatingPointFormat.decimalOneDigitTwoExponent_midpoint_one_two_rounds_to_two`,
`FloatingPointFormat.problem2_8_decimal_midpoint_strict_between_violated`,
`FloatingPointFormat.decimalOneDigitThreeExponentFormat_three_halves_not_finiteSystem`,
`FloatingPointFormat.problem2_8_finiteRoundToEven_guarded_sequence_counterexample`,
`FloatingPointFormat.problem2_8_guarded_sequence_counterexample_missing_midpoint_finiteSystem`,
`FloatingPointFormat.problem2_8_exact_guarded_midpoint_strict_between`,
`FloatingPointFormat.problem2_8_guarded_exact_operation_sequence_eq_exact_midpoint`,
`FloatingPointFormat.problem2_8_guarded_exact_operation_sequence_strict_between`,
`FloatingPointFormat.problem2_8_guarded_sequence_eq_exact_midpoint_of_finite_midpoint_steps`,
`FloatingPointFormat.problem2_8_guarded_sequence_strict_between_of_finite_midpoint_steps`,
and
`FloatingPointFormat.problem2_8_guarded_sequence_strict_between_of_sterbenz_subtraction`.
This closes the first sentence of Problem 2.8: in a one-digit decimal format,
`1` and `2` are floating-point numbers with `1 < 2`, but
`fl((1+2)/2) = fl(3/2) = 2`, so the strict upper inequality in
`1 < fl((1+2)/2) < 2` fails.  The second theorem audits the guard-digit
sentence: in the one-digit decimal format with `1/2` representable, the
operation sequence has exact `2-1` and exact division by `2`, but the final
round-to-even addition `1+1/2` returns `2`, so the strict inequality still
fails for the naive finite round-to-even operation-sequence interpretation.
The missing-hypothesis theorem proves this same witness has finite `2-1` and
finite `(2-1)/2`, but nonfinite final midpoint `1+(2-1)/2 = 3/2`.
The positive corrected theorem proves that the exact guarded midpoint is
strictly between the endpoints.  The exact-operation wrappers prove that any
operation model with exact subtraction, exact halving, and exact final addition
computes that interior midpoint; the finite-selector theorem proves the same
for any finite format when the exact subtraction, half-difference, and final
midpoint are all finite representable.  The Sterbenz-specialized theorem
discharges the exact subtraction condition from finite endpoints plus
Sterbenz's ratio condition.  The remaining Problem 2.8 work is a concrete full
guard-digit/IEEE operation-semantics lift beyond this exact-step theorem
surface.

Chapter 2 double-rounding counterexample (§2.3 / Problem 2.9):
`FloatingPointFormat.binaryT2DoubleRoundingDestinationFormat`,
`FloatingPointFormat.binaryT3DoubleRoundingExtendedFormat`,
`FloatingPointFormat.binaryT3DoubleRounding_rounds_21_16_to_5_4`,
`FloatingPointFormat.binaryT2DoubleRounding_rounds_5_4_to_1`,
`FloatingPointFormat.binaryT2DoubleRounding_rounds_21_16_to_3_2`, and
`FloatingPointFormat.binaryDoubleRounding_counterexample` give a small finite
binary round-to-even witness for the source warning that extended precision
followed by destination rounding can differ from direct destination rounding:
`21/16` rounds through the `t = 3` format to `5/4` and then through the `t = 2`
format to `1`, while direct `t = 2` rounding gives `3/2`.  The exact Problem
2.9 calculation for `sqrt(1 - 2^-53)` is closed at the finite selector layer by
`FloatingPointFormat.problem2_9_direct_double_rounds_to_predecessor`,
`FloatingPointFormat.problem2_9_direct_double_sqrt_rounds_to_predecessor`,
`FloatingPointFormat.problem2_9_extended64_rounds_to_double_midpoint`,
`FloatingPointFormat.problem2_9_double_rounds_extended_midpoint_to_one`,
`FloatingPointFormat.problem2_9_double_rounding_from_extended64`, and
`FloatingPointFormat.problem2_9_direct_double_ne_double_rounded_extended64`:
direct IEEE-double finite round-to-even gives `1 - 2^-53`, while rounding first
to the local 64-bit-mantissa extended format gives the double midpoint
`1 - 2^-54` and the final double rounding ties to even at `1`.  Full IEEE
operation semantics with flags, traps, signaling NaNs, payloads, and all special
values remain open.

Chapter 2 Kahan theorem empirical exercise (Problem 2.10):
The book instruction to test Kahan's theorem on a reader's computer is classified as `empirical-source-output`: no concrete computer, program, compiler/runtime, storage/reload behavior, exceptional behavior, or formatting convention is supplied.  The Lean facts below are retained only as optional modeled finite-selector artifacts around the mathematical mechanism, not as an active Chapter 2 proof gate; future P2.10 work should be an experiment unless a fully specified machine model is explicitly supplied.

`FloatingPointFormat.problem2_10_displayed_denominator_eq_power_sum`,
`FloatingPointFormat.problem2_10_powerOfTwo_numerator_kahan_hypotheses`,
`FloatingPointFormat.problem2_10_negative_powerOfTwo_numerator_kahan_hypotheses`,
`FloatingPointFormat.problem2_10_allowableDenominator`,
`FloatingPointFormat.problem2_10_allowableDenominator_of_nat_power_sum`,
`FloatingPointFormat.problem2_10_allowableDenominator_ne_zero`,
`FloatingPointFormat.problem2_10_kahan_integer_hypotheses_of_allowableDenominator`,
`FloatingPointFormat.problem2_10_powerOfTwo_numerator_kahan_hypotheses_of_allowableDenominator`,
`FloatingPointFormat.problem2_10_negative_powerOfTwo_numerator_kahan_hypotheses_of_allowableDenominator`,
`FloatingPointFormat.problem2_10_displayedAllowableDenominatorPrefix`,
`FloatingPointFormat.problem2_10_displayedAllowableDenominatorPrefix_allowable`,
`FloatingPointFormat.problem2_10_denominator_five_eq_power_sum`,
`FloatingPointFormat.problem2_10_five_allowableDenominator`,
`FloatingPointFormat.problem2_10_denominator_six_eq_power_sum`,
`FloatingPointFormat.problem2_10_six_allowableDenominator`,
`FloatingPointFormat.problem2_10_denominator_nine_eq_power_sum`,
`FloatingPointFormat.problem2_10_nine_allowableDenominator`,
`FloatingPointFormat.problem2_10_denominator_ten_eq_power_sum`,
`FloatingPointFormat.problem2_10_ten_allowableDenominator`,
`FloatingPointFormat.problem2_10_denominator_twelve_eq_power_sum`,
`FloatingPointFormat.problem2_10_twelve_allowableDenominator`,
`FloatingPointFormat.problem2_10_denominator_seventeen_eq_power_sum`,
`FloatingPointFormat.problem2_10_seventeen_allowableDenominator`,
`FloatingPointFormat.problem2_10_denominator_eighteen_eq_power_sum`,
`FloatingPointFormat.problem2_10_eighteen_allowableDenominator`,
`FloatingPointFormat.problem2_10_denominator_twenty_eq_power_sum`,
`FloatingPointFormat.problem2_10_twenty_allowableDenominator`,
`FloatingPointFormat.problem2_10_denominator_thirtythree_eq_power_sum`,
`FloatingPointFormat.problem2_10_thirtythree_allowableDenominator`,
`FloatingPointFormat.problem2_10_denominator_sixtyfive_eq_power_sum`,
`FloatingPointFormat.problem2_10_sixtyfive_allowableDenominator`,
`FloatingPointFormat.problem2_10_denominator_onehundredtwentynine_eq_power_sum`,
`FloatingPointFormat.problem2_10_onehundredtwentynine_allowableDenominator`,
`FloatingPointFormat.problem2_10_denominator_twohundredfiftyseven_eq_power_sum`,
`FloatingPointFormat.problem2_10_twohundredfiftyseven_allowableDenominator`,
`FloatingPointFormat.problem2_10_denominator_fivehundredthirteen_eq_power_sum`,
`FloatingPointFormat.problem2_10_fivehundredthirteen_allowableDenominator`,
`FloatingPointFormat.problem2_10_denominator_onethousandtwentyfive_eq_power_sum`,
`FloatingPointFormat.problem2_10_onethousandtwentyfive_allowableDenominator`,
`FloatingPointFormat.problem2_10_denominator_twothousandfortynine_eq_power_sum`,
`FloatingPointFormat.problem2_10_twothousandfortynine_allowableDenominator`,
`FloatingPointFormat.problem2_10_denominator_fourthousandninetyseven_eq_power_sum`,
`FloatingPointFormat.problem2_10_fourthousandninetyseven_allowableDenominator`,
`FloatingPointFormat.problem2_10_denominator_eightthousandonehundredninetythree_eq_power_sum`,
`FloatingPointFormat.problem2_10_eightthousandonehundredninetythree_allowableDenominator`,
`FloatingPointFormat.problem2_10_denominator_sixteenthousandthreehundredeightyfive_eq_power_sum`,
`FloatingPointFormat.problem2_10_sixteenthousandthreehundredeightyfive_allowableDenominator`,
`FloatingPointFormat.problem2_10_denominator_thirtytwothousandsevenhundredsixtynine_eq_power_sum`,
`FloatingPointFormat.problem2_10_thirtytwothousandsevenhundredsixtynine_allowableDenominator`,
`FloatingPointFormat.problem2_10_denominator_sixtyfivethousandfivehundredthirtyseven_eq_power_sum`,
`FloatingPointFormat.problem2_10_sixtyfivethousandfivehundredthirtyseven_allowableDenominator`,
`FloatingPointFormat.problem2_10_denominator_onehundredthirtyonethousandseventythree_eq_power_sum`,
`FloatingPointFormat.problem2_10_onehundredthirtyonethousandseventythree_allowableDenominator`,
`FloatingPointFormat.problem2_10_denominator_twohundredsixtytwothousandonehundredfortyfive_eq_power_sum`,
`FloatingPointFormat.problem2_10_twohundredsixtytwothousandonehundredfortyfive_allowableDenominator`,
`FloatingPointFormat.problem2_10_denominator_fivehundredtwentyfourthousandtwohundredeightynine_eq_power_sum`,
`FloatingPointFormat.problem2_10_fivehundredtwentyfourthousandtwohundredeightynine_allowableDenominator`,
`FloatingPointFormat.problem2_10_denominator_onemillionfortyeightthousandfivehundredseventyseven_eq_power_sum`,
`FloatingPointFormat.problem2_10_onemillionfortyeightthousandfivehundredseventyseven_allowableDenominator`,
`FloatingPointFormat.problem2_10_denominator_twomillionninetyseventhousandonehundredfiftythree_eq_power_sum`,
`FloatingPointFormat.problem2_10_twomillionninetyseventhousandonehundredfiftythree_allowableDenominator`,
`FloatingPointFormat.problem2_10_one_sixth_kahan_hypotheses`,
`FloatingPointFormat.problem2_10_negative_one_sixth_kahan_hypotheses`,
`FloatingPointFormat.problem2_10_one_tenth_kahan_hypotheses`,
`FloatingPointFormat.problem2_10_negative_one_tenth_kahan_hypotheses`,
`FloatingPointFormat.problem2_10_two_pow_succ_numerator_kahan_hypotheses_of_ten`,
`FloatingPointFormat.problem2_10_negative_two_pow_succ_numerator_kahan_hypotheses_of_ten`,
`FloatingPointFormat.problem2_10_two_pow_add_two_numerator_kahan_hypotheses_of_twelve`,
`FloatingPointFormat.problem2_10_negative_two_pow_add_two_numerator_kahan_hypotheses_of_twelve`,
`FloatingPointFormat.problem2_10_two_pow_succ_numerator_kahan_hypotheses_of_eighteen`,
`FloatingPointFormat.problem2_10_negative_two_pow_succ_numerator_kahan_hypotheses_of_eighteen`,
`FloatingPointFormat.problem2_10_two_pow_add_two_numerator_kahan_hypotheses_of_twenty`,
`FloatingPointFormat.problem2_10_negative_two_pow_add_two_numerator_kahan_hypotheses_of_twenty`,
`FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_nine`,
`FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_nine`,
`FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_seventeen`,
`FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_seventeen`,
`FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_thirtythree`,
`FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_thirtythree`,
`FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_sixtyfive`,
`FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_sixtyfive`,
`FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_onehundredtwentynine`,
`FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_onehundredtwentynine`,
`FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_twohundredfiftyseven`,
`FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_twohundredfiftyseven`,
`FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_fivehundredthirteen`,
`FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_fivehundredthirteen`,
`FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_onethousandtwentyfive`,
`FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_onethousandtwentyfive`,
`FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_twothousandfortynine`,
`FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_twothousandfortynine`,
`FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_fourthousandninetyseven`,
`FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_fourthousandninetyseven`,
`FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_eightthousandonehundredninetythree`,
`FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_eightthousandonehundredninetythree`,
`FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_sixteenthousandthreehundredeightyfive`,
`FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_sixteenthousandthreehundredeightyfive`,
`FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_thirtytwothousandsevenhundredsixtynine`,
`FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_thirtytwothousandsevenhundredsixtynine`,
`FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_sixtyfivethousandfivehundredthirtyseven`,
`FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_sixtyfivethousandfivehundredthirtyseven`,
`FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_onehundredthirtyonethousandseventythree`,
`FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_onehundredthirtyonethousandseventythree`,
`FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_twohundredsixtytwothousandonehundredfortyfive`,
`FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_twohundredsixtytwothousandonehundredfortyfive`,
`FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_fivehundredtwentyfourthousandtwohundredeightynine`,
`FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_fivehundredtwentyfourthousandtwohundredeightynine`,
`FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_onemillionfortyeightthousandfivehundredseventyseven`,
`FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_onemillionfortyeightthousandfivehundredseventyseven`,
`FloatingPointFormat.problem2_10_two_pow_numerator_kahan_hypotheses_of_twomillionninetyseventhousandonehundredfiftythree`,
`FloatingPointFormat.problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_twomillionninetyseventhousandonehundredfiftythree`,
`FloatingPointFormat.problem2_10_one_fifth_kahan_hypotheses`,
`FloatingPointFormat.problem2_10_negative_one_fifth_kahan_hypotheses`,
`FloatingPointFormat.problem2_10_two_fifth_kahan_hypotheses`,
`FloatingPointFormat.problem2_10_negative_two_fifth_kahan_hypotheses`,
`FloatingPointFormat.problem2_10_three_fifth_kahan_hypotheses`,
`FloatingPointFormat.problem2_10_negative_three_fifth_kahan_hypotheses`,
`FloatingPointFormat.problem2_10_three_mul_powerOfTwo_numerator_kahan_hypotheses_of_five`,
`FloatingPointFormat.problem2_10_negative_three_mul_powerOfTwo_numerator_kahan_hypotheses_of_five`,
`FloatingPointFormat.problem2_10_ieeeDouble_finiteSystem_five`,
`FloatingPointFormat.problem2_10_ieeeDouble_one_fifth_trace_finite_inputs`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_one_fifth_trace_finite_inputs`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_fifth_trace_finite_inputs`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_two_fifth_trace_finite_inputs`,
`FloatingPointFormat.problem2_10_ieeeDouble_three_fifth_trace_finite_inputs`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_three_fifth_trace_finite_inputs`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_le_maxFiniteMagnitude`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_three_finiteNormalRange`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_thirds_rounds_to_lower`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_three`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_thirds_mul_three_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_three_exact_mul_three_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_midpoint_below_two_pow_rounds_to_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_thirds_times_three`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_three`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_thirds_mul_three_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_three_exact_mul_three_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_midpoint_above_two_pow_rounds_to_neg_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_thirds_times_three`,
`FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_thirds_times_three`,
`FloatingPointFormat.problem2_10_finiteRoundToEven_div_mul_exact_of_finiteSystem`,
`FloatingPointFormat.problem2_10_ieeeDouble_zero_allowable_denominator_times_denominator'`,
`FloatingPointFormat.problem2_10_ieeeDouble_allowable_denominator_exact_quotient_trace`,
`FloatingPointFormat.problem2_10_ieeeDouble_oneFifth_rounds_to_upper`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_one_five`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_oneFifth_mul_five_above_one`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_one_five_exact_mul_five_above_one`,
`FloatingPointFormat.problem2_10_ieeeDouble_one_plus_two_pow_neg54_rounds_to_one`,
`FloatingPointFormat.problem2_10_ieeeDouble_one_fifth_times_five`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_one_five`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_oneFifth_mul_five_below_neg_one`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_one_five_exact_mul_five_below_neg_one`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_one_plus_two_pow_neg54_rounds_to_neg_one`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_one_fifth_times_five`,
`FloatingPointFormat.problem2_10_ieeeDouble_signed_one_fifth_times_five`,
`FloatingPointFormat.problem2_10_ieeeDouble_twoFifths_rounds_to_upper`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_five`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_twoFifths_mul_five_above_two`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_five_exact_mul_five_above_two`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_plus_two_pow_neg53_rounds_to_two`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_fifth_times_five`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_five`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_twoFifths_mul_five_below_neg_two`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_five_exact_mul_five_below_neg_two`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_two_plus_two_pow_neg53_rounds_to_neg_two`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_two_fifth_times_five`,
`FloatingPointFormat.problem2_10_ieeeDouble_signed_two_fifth_times_five`,
`FloatingPointFormat.problem2_10_ieeeDouble_threeFifths_rounds_to_lower`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_three_five`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_threeFifths_mul_five_below_three`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_three_five_exact_mul_five_below_three`,
`FloatingPointFormat.problem2_10_ieeeDouble_three_minus_two_pow_neg53_rounds_to_three`,
`FloatingPointFormat.problem2_10_ieeeDouble_three_fifth_times_five`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_three_five`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_threeFifths_mul_five_above_neg_three`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_three_five_exact_mul_five_above_neg_three`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_three_minus_two_pow_neg53_rounds_to_neg_three`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_three_fifth_times_five`,
`FloatingPointFormat.problem2_10_ieeeDouble_signed_three_fifth_times_five`,
`FloatingPointFormat.problem2_10_ieeeDouble_three_mul_two_pow_div_five_finiteNormalRange`,
`FloatingPointFormat.problem2_10_ieeeDouble_three_mul_two_pow_fifths_rounds_to_lower`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_three_mul_two_pow_five`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_three_mul_two_pow_fifths_mul_five_below`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_three_mul_two_pow_five_exact_mul_five_below`,
`FloatingPointFormat.problem2_10_ieeeDouble_three_mul_two_pow_minus_quarter_ulp_rounds`,
`FloatingPointFormat.problem2_10_ieeeDouble_three_mul_two_pow_fifths_times_five`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_three_mul_two_pow_five`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_three_mul_two_pow_fifths_mul_five_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_three_mul_two_pow_five_exact_mul_five_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_three_mul_two_pow_minus_quarter_ulp_rounds`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_three_mul_two_pow_fifths_times_five`,
`FloatingPointFormat.problem2_10_ieeeDouble_signed_three_mul_two_pow_fifths_times_five`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_five_finiteNormalRange`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_fifths_rounds_to_upper`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_five`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_fifths_mul_five_above_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_five_exact_mul_five_above_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_plus_quarter_ulp_rounds_to_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_fifths_times_five`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_five`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_fifths_mul_five_below_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_five_exact_mul_five_below_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_two_pow_plus_quarter_ulp_rounds_to_neg_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_fifths_times_five`,
`FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_fifths_times_five`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_nine_finiteNormalRange`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_ninths_rounds_to_lower`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_nine`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_ninths_mul_nine_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_nine_exact_mul_nine_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_ninths_times_nine`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_nine`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_ninths_mul_nine_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_nine_exact_mul_nine_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_ninths_times_nine`,
`FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_ninths_times_nine`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_minus_one_sixteenth_ulp_rounds_to_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_seventeen_finiteNormalRange`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_seventeenths_rounds_to_lower`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_seventeen`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_seventeenths_mul_seventeen_below`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_seventeen_exact_mul_seventeen_below`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_seventeenths_times_seventeen`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_seventeen`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_seventeenths_mul_seventeen_below`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_seventeen_exact_mul_seventeen_below`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_two_pow_minus_one_sixteenth_ulp_rounds_to_neg_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_seventeenths_times_seventeen`,
`FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_seventeenths_times_seventeen`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_plus_one_eighth_ulp_rounds_to_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_thirtythree_finiteNormalRange`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_thirtythirds_rounds_to_upper`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_thirtythree`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_thirtythirds_mul_thirtythree_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_thirtythree_exact_mul_thirtythree_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_thirtythirds_times_thirtythree`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_thirtythree`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_thirtythirds_mul_thirtythree_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_thirtythree_exact_mul_thirtythree_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_two_pow_plus_one_eighth_ulp_rounds_to_neg_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_thirtythirds_times_thirtythree`,
`FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_thirtythirds_times_thirtythree`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_sixtyfive_finiteNormalRange`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_sixtyfifths_rounds_to_upper`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_sixtyfive`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_sixtyfifths_mul_sixtyfive_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_sixtyfive_exact_mul_sixtyfive_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_sixtyfifths_times_sixtyfive`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_sixtyfive`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_sixtyfifths_mul_sixtyfive_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_sixtyfive_exact_mul_sixtyfive_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_sixtyfifths_times_sixtyfive`,
`FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_sixtyfifths_times_sixtyfive`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_onehundredtwentynine_finiteNormalRange`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_onehundredtwentyninths_rounds_to_lower`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_onehundredtwentynine`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_onehundredtwentyninths_mul_onehundredtwentynine_below`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_onehundredtwentynine_exact_mul_onehundredtwentynine_below`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_onehundredtwentyninths_times_onehundredtwentynine`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_onehundredtwentynine`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_onehundredtwentyninths_mul_onehundredtwentynine_below`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_onehundredtwentynine_exact_mul_onehundredtwentynine_below`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_onehundredtwentyninths_times_onehundredtwentynine`,
`FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_onehundredtwentyninths_times_onehundredtwentynine`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_plus_one_sixteenth_ulp_rounds_to_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_twohundredfiftyseven_finiteNormalRange`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_twohundredfiftysevenths_rounds_to_upper`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_twohundredfiftyseven`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_twohundredfiftysevenths_mul_twohundredfiftyseven_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_twohundredfiftyseven_exact_mul_twohundredfiftyseven_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_twohundredfiftysevenths_times_twohundredfiftyseven`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_twohundredfiftyseven`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_twohundredfiftysevenths_mul_twohundredfiftyseven_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_twohundredfiftyseven_exact_mul_twohundredfiftyseven_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_two_pow_plus_one_sixteenth_ulp_rounds_to_neg_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_twohundredfiftysevenths_times_twohundredfiftyseven`,
`FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_twohundredfiftysevenths_times_twohundredfiftyseven`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_fivehundredthirteen_finiteNormalRange`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_fivehundredthirteenths_rounds_to_lower`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_fivehundredthirteen`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_fivehundredthirteenths_mul_fivehundredthirteen_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_fivehundredthirteen_exact_mul_fivehundredthirteen_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_fivehundredthirteenths_times_fivehundredthirteen`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_fivehundredthirteen`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_fivehundredthirteenths_mul_fivehundredthirteen_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_fivehundredthirteen_exact_mul_fivehundredthirteen_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_fivehundredthirteenths_times_fivehundredthirteen`,
`FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_fivehundredthirteenths_times_fivehundredthirteen`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_minus_one_twohundredfiftysixth_ulp_rounds_to_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_two_pow_minus_one_twohundredfiftysixth_ulp_rounds_to_neg_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_onethousandtwentyfive_finiteNormalRange`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_onethousandtwentyfifths_rounds_to_lower`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_onethousandtwentyfive`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_onethousandtwentyfifths_mul_onethousandtwentyfive_below`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_onethousandtwentyfive_exact_mul_onethousandtwentyfive_below`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_onethousandtwentyfifths_times_onethousandtwentyfive`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_onethousandtwentyfive`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_onethousandtwentyfifths_mul_onethousandtwentyfive_below`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_onethousandtwentyfive_exact_mul_onethousandtwentyfive_below`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_onethousandtwentyfifths_times_onethousandtwentyfive`,
`FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_onethousandtwentyfifths_times_onethousandtwentyfive`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_twothousandfortynine_finiteNormalRange`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_twothousandfortyninths_rounds_to_upper`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_twothousandfortynine`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_twothousandfortyninths_mul_twothousandfortynine_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_twothousandfortynine_exact_mul_twothousandfortynine_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_twothousandfortyninths_times_twothousandfortynine`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_twothousandfortynine`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_twothousandfortyninths_mul_twothousandfortynine_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_twothousandfortynine_exact_mul_twothousandfortynine_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_twothousandfortyninths_times_twothousandfortynine`,
`FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_twothousandfortyninths_times_twothousandfortynine`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_plus_one_twohundredfiftysixth_ulp_rounds_to_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_two_pow_plus_one_twohundredfiftysixth_ulp_rounds_to_neg_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_fourthousandninetyseven_finiteNormalRange`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_fourthousandninetysevenths_rounds_to_upper`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_fourthousandninetyseven`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_fourthousandninetysevenths_mul_fourthousandninetyseven_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_fourthousandninetyseven_exact_mul_fourthousandninetyseven_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_fourthousandninetysevenths_times_fourthousandninetyseven`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_fourthousandninetyseven`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_fourthousandninetysevenths_mul_fourthousandninetyseven_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_fourthousandninetyseven_exact_mul_fourthousandninetyseven_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_fourthousandninetysevenths_times_fourthousandninetyseven`,
`FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_fourthousandninetysevenths_times_fourthousandninetyseven`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_plus_one_eightthousandonehundredninetysecond_ulp_rounds_to_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_two_pow_plus_one_eightthousandonehundredninetysecond_ulp_rounds_to_neg_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_eightthousandonehundredninetythree_finiteNormalRange`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_eightthousandonehundredninetythirds_rounds_to_upper`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_eightthousandonehundredninetythree`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_eightthousandonehundredninetythirds_mul_eightthousandonehundredninetythree_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_eightthousandonehundredninetythree_exact_mul_eightthousandonehundredninetythree_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_eightthousandonehundredninetythirds_times_eightthousandonehundredninetythree`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_eightthousandonehundredninetythree`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_eightthousandonehundredninetythirds_mul_eightthousandonehundredninetythree_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_eightthousandonehundredninetythree_exact_mul_eightthousandonehundredninetythree_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_eightthousandonehundredninetythirds_times_eightthousandonehundredninetythree`,
`FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_eightthousandonehundredninetythirds_times_eightthousandonehundredninetythree`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_sixteenthousandthreehundredeightyfive_finiteNormalRange`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_sixteenthousandthreehundredeightyfifths_rounds_to_lower`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_sixteenthousandthreehundredeightyfive`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_sixteenthousandthreehundredeightyfifths_mul_sixteenthousandthreehundredeightyfive_below`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_sixteenthousandthreehundredeightyfive_exact_mul_sixteenthousandthreehundredeightyfive_below`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_sixteenthousandthreehundredeightyfifths_times_sixteenthousandthreehundredeightyfive`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_sixteenthousandthreehundredeightyfive`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_sixteenthousandthreehundredeightyfifths_mul_sixteenthousandthreehundredeightyfive_below`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_sixteenthousandthreehundredeightyfive_exact_mul_sixteenthousandthreehundredeightyfive_below`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_sixteenthousandthreehundredeightyfifths_times_sixteenthousandthreehundredeightyfive`,
`FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_sixteenthousandthreehundredeightyfifths_times_sixteenthousandthreehundredeightyfive`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_thirtytwothousandsevenhundredsixtynine_finiteNormalRange`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_thirtytwothousandsevenhundredsixtyninths_rounds_to_lower`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_thirtytwothousandsevenhundredsixtynine`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_thirtytwothousandsevenhundredsixtyninths_mul_thirtytwothousandsevenhundredsixtynine_below`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_thirtytwothousandsevenhundredsixtynine_exact_mul_thirtytwothousandsevenhundredsixtynine_below`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_thirtytwothousandsevenhundredsixtyninths_times_thirtytwothousandsevenhundredsixtynine`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_thirtytwothousandsevenhundredsixtynine`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_thirtytwothousandsevenhundredsixtyninths_mul_thirtytwothousandsevenhundredsixtynine_below`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_thirtytwothousandsevenhundredsixtynine_exact_mul_thirtytwothousandsevenhundredsixtynine_below`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_thirtytwothousandsevenhundredsixtyninths_times_thirtytwothousandsevenhundredsixtynine`,
`FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_thirtytwothousandsevenhundredsixtyninths_times_thirtytwothousandsevenhundredsixtynine`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_minus_one_fourthousandninetysixth_ulp_rounds_to_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_two_pow_minus_one_fourthousandninetysixth_ulp_rounds_to_neg_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_sixtyfivethousandfivehundredthirtyseven_finiteNormalRange`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_sixtyfivethousandfivehundredthirtysevenths_rounds_to_lower`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_sixtyfivethousandfivehundredthirtyseven`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_sixtyfivethousandfivehundredthirtysevenths_mul_sixtyfivethousandfivehundredthirtyseven_below`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_sixtyfivethousandfivehundredthirtyseven_exact_mul_sixtyfivethousandfivehundredthirtyseven_below`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_sixtyfivethousandfivehundredthirtysevenths_times_sixtyfivethousandfivehundredthirtyseven`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_sixtyfivethousandfivehundredthirtyseven`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_sixtyfivethousandfivehundredthirtysevenths_mul_sixtyfivethousandfivehundredthirtyseven_below`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_sixtyfivethousandfivehundredthirtyseven_exact_mul_sixtyfivethousandfivehundredthirtyseven_below`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_sixtyfivethousandfivehundredthirtysevenths_times_sixtyfivethousandfivehundredthirtyseven`,
`FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_sixtyfivethousandfivehundredthirtysevenths_times_sixtyfivethousandfivehundredthirtyseven`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_minus_one_sixtythreethousandfivehundredthirtysixth_ulp_rounds_to_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_two_pow_minus_one_sixtythreethousandfivehundredthirtysixth_ulp_rounds_to_neg_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_onehundredthirtyonethousandseventythree_finiteNormalRange`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_onehundredthirtyonethousandseventythirds_rounds_to_lower`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_onehundredthirtyonethousandseventythree`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_onehundredthirtyonethousandseventythirds_mul_onehundredthirtyonethousandseventythree_below`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_onehundredthirtyonethousandseventythree_exact_mul_onehundredthirtyonethousandseventythree_below`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_onehundredthirtyonethousandseventythirds_times_onehundredthirtyonethousandseventythree`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_onehundredthirtyonethousandseventythree`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_onehundredthirtyonethousandseventythirds_mul_onehundredthirtyonethousandseventythree_below`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_onehundredthirtyonethousandseventythree_exact_mul_onehundredthirtyonethousandseventythree_below`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_onehundredthirtyonethousandseventythirds_times_onehundredthirtyonethousandseventythree`,
`FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_onehundredthirtyonethousandseventythirds_times_onehundredthirtyonethousandseventythree`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_twohundredsixtytwothousandonehundredfortyfive_finiteNormalRange`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_twohundredsixtytwothousandonehundredfortyfifths_rounds_to_upper`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_twohundredsixtytwothousandonehundredfortyfive`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_twohundredsixtytwothousandonehundredfortyfifths_mul_twohundredsixtytwothousandonehundredfortyfive_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_twohundredsixtytwothousandonehundredfortyfive_exact_mul_twohundredsixtytwothousandonehundredfortyfive_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_twohundredsixtytwothousandonehundredfortyfifths_times_twohundredsixtytwothousandonehundredfortyfive`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_twohundredsixtytwothousandonehundredfortyfive`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_twohundredsixtytwothousandonehundredfortyfifths_mul_twohundredsixtytwothousandonehundredfortyfive_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_twohundredsixtytwothousandonehundredfortyfive_exact_mul_twohundredsixtytwothousandonehundredfortyfive_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_twohundredsixtytwothousandonehundredfortyfifths_times_twohundredsixtytwothousandonehundredfortyfive`,
`FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_twohundredsixtytwothousandonehundredfortyfifths_times_twohundredsixtytwothousandonehundredfortyfive`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_plus_one_thirtysecond_ulp_rounds_to_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_two_pow_plus_one_thirtysecond_ulp_rounds_to_neg_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_plus_one_sixtyfourth_ulp_rounds_to_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_two_pow_plus_one_sixtyfourth_ulp_rounds_to_neg_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_plus_one_onehundredtwentyeighth_ulp_rounds_to_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_two_pow_plus_one_onehundredtwentyeighth_ulp_rounds_to_neg_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_plus_one_fivehundredtwelfth_ulp_rounds_to_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_two_pow_plus_one_fivehundredtwelfth_ulp_rounds_to_neg_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_plus_one_onethousandtwentyfourth_ulp_rounds_to_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_two_pow_plus_one_onethousandtwentyfourth_ulp_rounds_to_neg_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_fivehundredtwentyfourthousandtwohundredeightynine_finiteNormalRange`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_fivehundredtwentyfourthousandtwohundredeightyninths_rounds_to_upper`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_fivehundredtwentyfourthousandtwohundredeightynine`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_fivehundredtwentyfourthousandtwohundredeightyninths_mul_fivehundredtwentyfourthousandtwohundredeightynine_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_fivehundredtwentyfourthousandtwohundredeightynine_exact_mul_fivehundredtwentyfourthousandtwohundredeightynine_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_fivehundredtwentyfourthousandtwohundredeightyninths_times_fivehundredtwentyfourthousandtwohundredeightynine`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_fivehundredtwentyfourthousandtwohundredeightynine`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_fivehundredtwentyfourthousandtwohundredeightyninths_mul_fivehundredtwentyfourthousandtwohundredeightynine_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_fivehundredtwentyfourthousandtwohundredeightynine_exact_mul_fivehundredtwentyfourthousandtwohundredeightynine_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_fivehundredtwentyfourthousandtwohundredeightyninths_times_fivehundredtwentyfourthousandtwohundredeightynine`,
`FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_fivehundredtwentyfourthousandtwohundredeightyninths_times_fivehundredtwentyfourthousandtwohundredeightynine`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_onemillionfortyeightthousandfivehundredseventyseven_finiteNormalRange`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_onemillionfortyeightthousandfivehundredseventysevenths_rounds_to_upper`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_onemillionfortyeightthousandfivehundredseventyseven`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_onemillionfortyeightthousandfivehundredseventysevenths_mul_onemillionfortyeightthousandfivehundredseventyseven_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_onemillionfortyeightthousandfivehundredseventyseven_exact_mul_onemillionfortyeightthousandfivehundredseventyseven_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_onemillionfortyeightthousandfivehundredseventysevenths_times_onemillionfortyeightthousandfivehundredseventyseven`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_onemillionfortyeightthousandfivehundredseventyseven`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_onemillionfortyeightthousandfivehundredseventysevenths_mul_onemillionfortyeightthousandfivehundredseventyseven_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_onemillionfortyeightthousandfivehundredseventyseven_exact_mul_onemillionfortyeightthousandfivehundredseventyseven_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_onemillionfortyeightthousandfivehundredseventysevenths_times_onemillionfortyeightthousandfivehundredseventyseven`,
`FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_onemillionfortyeightthousandfivehundredseventysevenths_times_onemillionfortyeightthousandfivehundredseventyseven`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_plus_one_twothousandfortyeighth_ulp_rounds_to_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_two_pow_plus_one_twothousandfortyeighth_ulp_rounds_to_neg_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_plus_one_fourthousandninetysixth_ulp_rounds_to_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_two_pow_plus_one_fourthousandninetysixth_ulp_rounds_to_neg_two_pow`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_div_twomillionninetyseventhousandonehundredfiftythree_finiteNormalRange`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_twomillionninetyseventhousandonehundredfiftythirds_rounds_to_upper`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_twomillionninetyseventhousandonehundredfiftythree`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_twomillionninetyseventhousandonehundredfiftythirds_mul_twomillionninetyseventhousandonehundredfiftythree_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_twomillionninetyseventhousandonehundredfiftythree_exact_mul_twomillionninetyseventhousandonehundredfiftythree_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_twomillionninetyseventhousandonehundredfiftythirds_times_twomillionninetyseventhousandonehundredfiftythree`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_twomillionninetyseventhousandonehundredfiftythree`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_twomillionninetyseventhousandonehundredfiftythirds_mul_twomillionninetyseventhousandonehundredfiftythree_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_twomillionninetyseventhousandonehundredfiftythree_exact_mul_twomillionninetyseventhousandonehundredfiftythree_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_twomillionninetyseventhousandonehundredfiftythirds_times_twomillionninetyseventhousandonehundredfiftythree`,
`FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_twomillionninetyseventhousandonehundredfiftythirds_times_twomillionninetyseventhousandonehundredfiftythree`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_succ_eighteen`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_succ_eighteenths_mul_eighteen_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_succ_eighteen_exact_mul_eighteen_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_succ_eighteenths_times_eighteen`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_succ_eighteen`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_succ_eighteenths_mul_eighteen_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_succ_eighteen_exact_mul_eighteen_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_succ_eighteenths_times_eighteen`,
`FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_succ_eighteenths_times_eighteen`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_succ_six`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_succ_sixths_mul_six_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_succ_six_exact_mul_six_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_succ_sixths_times_six`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_succ_six`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_succ_sixths_mul_six_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_succ_six_exact_mul_six_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_succ_sixths_times_six`,
`FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_succ_sixths_times_six`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_succ_ten`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_succ_tenths_mul_ten_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_succ_ten_exact_mul_ten_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_succ_tenths_times_ten`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_succ_ten`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_succ_tenths_mul_ten_below`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_succ_ten_exact_mul_ten_below`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_succ_tenths_times_ten`,
`FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_succ_tenths_times_ten`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_add_two_twelve`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_add_two_twelfths_mul_twelve_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_add_two_twelve_exact_mul_twelve_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_add_two_twelfths_times_twelve`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_add_two_twelve`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_add_two_twelfths_mul_twelve_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_add_two_twelve_exact_mul_twelve_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_add_two_twelfths_times_twelve`,
`FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_add_two_twelfths_times_twelve`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_add_two_twenty`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_two_pow_add_two_twentieths_mul_twenty_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_pow_add_two_twenty_exact_mul_twenty_above`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_pow_add_two_twentieths_times_twenty`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_add_two_twenty`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_two_pow_add_two_twentieths_mul_twenty_below`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_pow_add_two_twenty_exact_mul_twenty_below`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_two_pow_add_two_twentieths_times_twenty`,
`FloatingPointFormat.problem2_10_ieeeDouble_signed_two_pow_add_two_twentieths_times_twenty`,
`FloatingPointFormat.problem2_10_ieeeDouble_oneSixth_rounds_to_lower`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_one_six`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_oneSixth_mul_six_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_one_six_exact_mul_six_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_one_sixth_times_six`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_one_six`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_oneSixth_mul_six_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_one_six_exact_mul_six_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_midpoint_above_one_rounds_to_neg_one`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_one_sixth_times_six`,
`FloatingPointFormat.problem2_10_ieeeDouble_signed_one_sixth_times_six`,
`FloatingPointFormat.problem2_10_ieeeDouble_oneTenth_rounds_to_upper`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_one_ten`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_oneTenth_mul_ten_above_one`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_one_ten_exact_mul_ten_above_one`,
`FloatingPointFormat.problem2_10_ieeeDouble_one_tenth_times_ten`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_one_ten`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_oneTenth_mul_ten_below_neg_one`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_one_ten_exact_mul_ten_below_neg_one`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_one_tenth_times_ten`,
`FloatingPointFormat.problem2_10_ieeeDouble_signed_one_tenth_times_ten`,
`FloatingPointFormat.problem2_10_displayed_kahan_hypotheses`,
`FloatingPointFormat.problem2_10_displayed_negative_kahan_hypotheses`,
`FloatingPointFormat.problem2_10_displayed_two_kahan_hypotheses`,
`FloatingPointFormat.problem2_10_displayed_negative_two_kahan_hypotheses`,
`FloatingPointFormat.problem2_10_displayed_four_kahan_hypotheses`,
`FloatingPointFormat.problem2_10_displayed_negative_four_kahan_hypotheses`,
`FloatingPointFormat.problem2_10_displayed_eight_kahan_hypotheses`,
`FloatingPointFormat.problem2_10_displayed_negative_eight_kahan_hypotheses`,
`FloatingPointFormat.problem2_10_displayed_sixteen_kahan_hypotheses`,
`FloatingPointFormat.problem2_10_displayed_negative_sixteen_kahan_hypotheses`,
`FloatingPointFormat.problem2_10_displayed_thirtytwo_kahan_hypotheses`,
`FloatingPointFormat.problem2_10_displayed_negative_thirtytwo_kahan_hypotheses`,
`FloatingPointFormat.problem2_10_ieeeDouble_finiteSystem_one`,
`FloatingPointFormat.problem2_10_ieeeDouble_finiteSystem_neg_one`,
`FloatingPointFormat.problem2_10_ieeeDouble_finiteSystem_two`,
`FloatingPointFormat.problem2_10_ieeeDouble_finiteSystem_neg_two`,
`FloatingPointFormat.problem2_10_ieeeDouble_finiteSystem_four`,
`FloatingPointFormat.problem2_10_ieeeDouble_finiteSystem_neg_four`,
`FloatingPointFormat.problem2_10_ieeeDouble_finiteSystem_eight`,
`FloatingPointFormat.problem2_10_ieeeDouble_finiteSystem_neg_eight`,
`FloatingPointFormat.problem2_10_ieeeDouble_finiteSystem_sixteen`,
`FloatingPointFormat.problem2_10_ieeeDouble_finiteSystem_neg_sixteen`,
`FloatingPointFormat.problem2_10_ieeeDouble_finiteSystem_thirtytwo`,
`FloatingPointFormat.problem2_10_ieeeDouble_finiteSystem_neg_thirtytwo`,
`FloatingPointFormat.problem2_10_ieeeDouble_finiteSystem_three`,
`FloatingPointFormat.problem2_10_ieeeDouble_finiteSystem_neg_three`,
`FloatingPointFormat.problem2_10_ieeeDouble_displayed_trace_finite_inputs`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_displayed_trace_finite_inputs`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_displayed_trace_finite_inputs`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_two_displayed_trace_finite_inputs`,
`FloatingPointFormat.problem2_10_ieeeDouble_four_displayed_trace_finite_inputs`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_four_displayed_trace_finite_inputs`,
`FloatingPointFormat.problem2_10_ieeeDouble_eight_displayed_trace_finite_inputs`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_eight_displayed_trace_finite_inputs`,
`FloatingPointFormat.problem2_10_ieeeDouble_sixteen_displayed_trace_finite_inputs`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_sixteen_displayed_trace_finite_inputs`,
`FloatingPointFormat.problem2_10_ieeeDouble_thirtytwo_displayed_trace_finite_inputs`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_thirtytwo_displayed_trace_finite_inputs`,
`FloatingPointFormat.problem2_10_finiteRoundToEven_zero_div_mul`,
`FloatingPointFormat.problem2_10_ieeeDouble_zero_allowable_denominator_times_denominator`,
`FloatingPointFormat.problem2_10_ieeeDouble_oneThird_rounds_to_lower`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_one_three`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_oneThird_mul_three_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_one_three_exact_mul_three_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_midpoint_below_one_rounds_to_one`,
`FloatingPointFormat.problem2_10_ieeeDouble_one_third_times_three`,
`FloatingPointFormat.problem2_10_ieeeDouble_twoThirds_rounds_to_lower`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_three`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_twoThirds_mul_three_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_two_three_exact_mul_three_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_midpoint_below_two_rounds_to_two`,
`FloatingPointFormat.problem2_10_ieeeDouble_two_thirds_times_three`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_one_three`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_oneThird_mul_three_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_one_three_exact_mul_three_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_midpoint_above_neg_one_rounds_to_neg_one`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_one_third_times_three`, and
`FloatingPointFormat.problem2_10_ieeeDouble_signed_one_third_times_three`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_three`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_twoThirds_mul_three_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_two_three_exact_mul_three_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_midpoint_above_two_rounds_to_neg_two`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_two_thirds_times_three`, and
`FloatingPointFormat.problem2_10_ieeeDouble_signed_two_thirds_times_three`,
`FloatingPointFormat.problem2_10_ieeeDouble_fourThirds_rounds_to_lower`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_four_three`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_fourThirds_mul_three_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_four_three_exact_mul_three_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_midpoint_below_four_rounds_to_four`,
`FloatingPointFormat.problem2_10_ieeeDouble_four_thirds_times_three`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_four_three`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_fourThirds_mul_three_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_four_three_exact_mul_three_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_midpoint_above_four_rounds_to_neg_four`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_four_thirds_times_three`, and
`FloatingPointFormat.problem2_10_ieeeDouble_signed_four_thirds_times_three`,
`FloatingPointFormat.problem2_10_ieeeDouble_eightThirds_rounds_to_lower`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_eight_three`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_eightThirds_mul_three_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_eight_three_exact_mul_three_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_midpoint_below_eight_rounds_to_eight`,
`FloatingPointFormat.problem2_10_ieeeDouble_eight_thirds_times_three`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_eight_three`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_eightThirds_mul_three_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_eight_three_exact_mul_three_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_midpoint_above_eight_rounds_to_neg_eight`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_eight_thirds_times_three`, and
`FloatingPointFormat.problem2_10_ieeeDouble_signed_eight_thirds_times_three`,
`FloatingPointFormat.problem2_10_ieeeDouble_sixteenThirds_rounds_to_lower`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_sixteen_three`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_sixteenThirds_mul_three_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_sixteen_three_exact_mul_three_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_midpoint_below_sixteen_rounds_to_sixteen`,
`FloatingPointFormat.problem2_10_ieeeDouble_sixteen_thirds_times_three`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_sixteen_three`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_sixteenThirds_mul_three_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_sixteen_three_exact_mul_three_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_midpoint_above_sixteen_rounds_to_neg_sixteen`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_sixteen_thirds_times_three`, and
`FloatingPointFormat.problem2_10_ieeeDouble_signed_sixteen_thirds_times_three`,
`FloatingPointFormat.problem2_10_ieeeDouble_thirtytwoThirds_rounds_to_lower`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_thirtytwo_three`,
`FloatingPointFormat.problem2_10_ieeeDouble_rounded_thirtytwoThirds_mul_three_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_thirtytwo_three_exact_mul_three_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_midpoint_below_thirtytwo_rounds_to_thirtytwo`,
`FloatingPointFormat.problem2_10_ieeeDouble_thirtytwo_thirds_times_three`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_thirtytwo_three`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_rounded_thirtytwoThirds_mul_three_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_div_neg_thirtytwo_three_exact_mul_three_midpoint`,
`FloatingPointFormat.problem2_10_ieeeDouble_negative_midpoint_above_thirtytwo_rounds_to_neg_thirtytwo`,
`FloatingPointFormat.problem2_10_ieeeDouble_neg_thirtytwo_thirds_times_three`, and
`FloatingPointFormat.problem2_10_ieeeDouble_signed_thirtytwo_thirds_times_three`.
These prove the displayed finite IEEE-double round-to-even instance and the
denominator-`3` signed extensions listed above.  Lean now records the source's
displayed allowable-denominator prefix
`1,2,3,4,5,6,8,9,10,12,16,17,18,20` at the integer-side shape
`n = 2^i + 2^j` using rational powers, so the leading `1` is represented as
`2^-1 + 2^-1`.  It also proves the generic denominator-`3` power-of-two
infrastructure needed by the quantified route: for every `k < t-1`, both
`m = 2^k` and `m = -2^k` satisfy the quoted integer-side Kahan hypotheses, and
for every `k <= 1023`, `(2^k)/3` lies in the IEEE-double finite-normal range
and finite IEEE-double round-to-even rounds it to the lower adjacent endpoint
`6004799503160661 * 2^(k-54)`.  Multiplying that rounded quotient exactly by
`3` gives the generic midpoint immediately below `2^k`, namely
`2^k - 2^(k-54)`, and the final tie-to-even step rounds that midpoint back
to `2^k`.  By round-to-even oddness, the signed companion is also closed:
`fl(((-2^k)/3)*3) = -2^k`.  Thus the signed denominator-`3`, power-of-two
numerator subfamily is closed in the finite IEEE-double round-to-even operation
wrapper for every `k <= 1023`.
It also records that the denominator-`3` signed numerator pairs
`m = ±1, ±2, ±4, ±8, ±16, ±32` satisfy the quoted integer-side Kahan hypotheses, that the
displayed operands and first rounded intermediates are finite IEEE-double
values, and that
the `m = 0` branch holds for every allowable natural denominator in the
finite-selector model, since allowable denominators are proved nonzero.  For
the displayed nonzero numerator Lean proves
`fl((1/3)*3) = 1`: `1/3` first rounds to
`6004799503160661 * 2^-54`, the actual exact product `fl(1/3)*3` is the
midpoint `1 - 2^-54`, and the final rounding ties to the even endpoint `1`.
The signed companion `m = -1`, `n = 3` is now also certified: `-1/3` rounds by
round-to-even oddness, the exact product is the midpoint `-1 + 2^-54`, and the
final rounding ties to `-1`.
The same denominator-`3` finite-selector trace is now closed for `m = 2` and
`m = -2`: `2/3` rounds to `6004799503160661 * 2^-53`, the exact product is the
midpoint `2 - 2^-53`, and the final tie rounds to `2`; the negative case
follows by oddness and ties to `-2`.
The denominator-`3` finite-selector trace is also closed for `m = 4` and
`m = -4`: `4/3` rounds to `6004799503160661 * 2^-52`, the exact product is the
midpoint `4 - 2^-52`, and the final tie rounds to `4`; the negative case
follows by oddness and ties to `-4`.
The same line-by-line trace is now closed for `m = 8` and `m = -8`: `8/3`
rounds to `6004799503160661 * 2^-51`, the exact product is the midpoint
`8 - 2^-51`, and the final tie rounds to `8`; the negative case follows by
oddness and ties to `-8`.
The denominator-`3` trace is now also closed for `m = 16` and `m = -16`:
`16/3` rounds to `6004799503160661 * 2^-50`, the exact product is the midpoint
`16 - 2^-50`, and the final tie rounds to `16`; the negative case follows by
oddness and ties to `-16`.
The denominator-`3` trace is now also closed for `m = 32` and `m = -32`:
`32/3` rounds to `6004799503160661 * 2^-49`, the exact product is the midpoint
`32 - 2^-49`, and the final tie rounds to `32`; the negative case follows by
oddness and ties to `-32`.
The allowable-denominator bookkeeping is now source-shaped: allowable
denominators are proved nonzero, natural power sums map into the
rational-exponent predicate, and the integer-side power-of-two numerator
hypotheses are available for arbitrary allowable denominators.  The
exact-quotient branch is also closed: if `m/n` and `m` are finite representable,
the modeled finite round-to-even division/multiplication sequence returns
`m`.  The first non-representable quotient case beyond denominator `3` is also
closed for `n = 5`, `m = ±1`: `1/5` rounds upward to
`7205759403792794 * 2^-55`, the exact product with `5` is `1 + 2^-54`, and
the final rounding returns `1`; the negative case follows by oddness.  The
next denominator-`5` numerator magnitude is also closed: `2/5` rounds upward
to `7205759403792794 * 2^-54`, the exact product with `5` is `2 + 2^-53`,
and the final rounding returns `2`.  The negative case again follows by
oddness.  The first denominator-`5` non-power-of-two numerator is now closed
too: `3/5` rounds downward to `5404319552844595 * 2^-53`, the exact product
with `5` is `3 - 2^-53`, and the final rounding returns `3`; the negative
case follows by oddness.  This non-power-of-two route is also scaled:
for `k <= 1021`, `(3*2^k)/5` rounds downward to
`5404319552844595 * 2^(k-53)`, the exact product with `5` is
`3*2^k - 2^(k-53)`, and the final rounding returns `3*2^k`; the signed
case follows by oddness.  More generally, the signed denominator-`5`,
power-of-two numerator subfamily is closed in the finite IEEE-double selector
model for `k <= 1022`:
`(2^k)/5` rounds upward to `7205759403792794 * 2^(k-55)`, the exact product
with `5` is `2^k + 2^(k-54)`, and the final rounding returns `2^k`; the
negative case follows by oddness.  The displayed denominator `9` is now closed
for power-of-two numerators as well: `9 = 2^3 + 2^0`, for `k <= 1023`,
`(2^k)/9` rounds downward to `8006399337547548 * 2^(k-56)`, the exact product
with `9` is the midpoint `2^k - 2^(k-54)`, and the final tie-to-even step
returns `2^k`, with the signed case by oddness.  The genuinely new
displayed-prefix denominator `17` is now closed for power-of-two numerators:
`17 = 2^4 + 2^0`, for `k <= 1023`, `(2^k)/17` rounds downward to
`8477364004462110 * 2^(k-57)`, the exact product with `17` is
`2^k - 2^(k-56)`, only one sixteenth of an ulp below `2^k`, and the final
rounding returns `2^k`; the signed case follows by oddness.  The next genuinely
new odd denominator `33` is also closed for power-of-two numerators:
`33 = 2^5 + 2^0`, for `k <= 1022`, `(2^k)/33` rounds upward to
`8734253822779144 * 2^(k-58)`, the exact product with `33` is
`2^k + 2^(k-55)`, one eighth of an ulp above `2^k`, and the final rounding
returns `2^k`; the signed case follows by oddness.  The next genuinely new
odd denominator `65` is also closed for power-of-two numerators:
`65 = 2^6 + 2^0`, for `k <= 1022`, `(2^k)/65` rounds upward to
`8868626958514208 * 2^(k-59)`, the exact product with `65` is
`2^k + 2^(k-54)`, one quarter of an ulp above `2^k`, and the final rounding
returns `2^k`; the signed case follows by oddness.  The next genuinely new
odd denominator `129` is also closed for power-of-two numerators:
`129 = 2^7 + 2^0`, for `k <= 1023`, `(2^k)/129` rounds downward to
`8937376004704240 * 2^(k-60)`, the exact product with `129` is
`2^k - 2^(k-56)`, one sixteenth of an ulp below `2^k`, and the final rounding
returns `2^k`; the signed case follows by oddness.  The next genuinely new
odd denominator `257` is also closed for power-of-two numerators:
`257 = 2^8 + 2^0`, for `k <= 1022`, `(2^k)/257` rounds upward to
`8972151786823712 * 2^(k-61)`, the exact product with `257` is
`2^k + 2^(k-56)`, one sixteenth of an ulp above `2^k`, and the final rounding
returns `2^k`; the signed case follows by oddness.  The next genuinely new
odd denominator `513` is also closed for power-of-two numerators:
`513 = 2^9 + 2^0`, for `k <= 1023`, `(2^k)/513` rounds downward to
`8989641361456896 * 2^(k-62)`, the exact product with `513` is the midpoint
`2^k - 2^(k-54)`, and the final tie-to-even rounding returns `2^k`; the
signed case follows by oddness.  The next genuinely new odd denominator `1025`
is also closed for power-of-two numerators: `1025 = 2^10 + 2^0`, for
`k <= 1023`, `(2^k)/1025` rounds downward to
`8998411743272952 * 2^(k-63)`, the exact product with `1025` is
`2^k - 2^(k-60)`, and the final round returns `2^k` because this value is
strictly closer to the power-of-two endpoint than to the previous double; the
signed case follows by oddness.  The next genuinely new odd denominator `2049`
is also closed for power-of-two numerators: `2049 = 2^11 + 2^0`, for
`k <= 1022`, `(2^k)/2049` rounds upward to
`9002803354665472 * 2^(k-64)`, the exact product with `2049` is
`2^k + 2^(k-55)`, one eighth of an ulp above `2^k`, and the final rounding
returns `2^k`; the signed case follows by oddness.  The next genuinely new
odd denominator `4097` is also closed for power-of-two numerators:
`4097 = 2^12 + 2^0`, for `k <= 1022`, `(2^k)/4097` rounds upward to
`9005000768225312 * 2^(k-65)`, the exact product with `4097` is
`2^k + 2^(k-60)`, one 256th of an ulp above `2^k`, and the final rounding
returns `2^k`; the signed case follows by oddness.  The next genuinely new
odd denominator `8193` is also closed for power-of-two numerators:
`8193 = 2^13 + 2^0`, for `k <= 1022`, `(2^k)/8193` rounds upward to
`9006099877314562 * 2^(k-66)`, the exact product with `8193` is
`2^k + 2^(k-65)`, one 8192nd of an ulp above `2^k`, and the final rounding
returns `2^k`; the signed case follows by oddness.  The next genuinely new
odd denominator `16385` is also closed for power-of-two numerators:
`16385 = 2^14 + 2^0`, for `k <= 1023`, `(2^k)/16385` rounds downward to
`9006649532479488 * 2^(k-67)`, the exact product with `16385` is
`2^k - 2^(k-56)`, one eighth of the lower ulp below `2^k`, and the final
rounding returns `2^k`; the signed case follows by oddness.  The next
genuinely new odd denominator `32769` is also closed for power-of-two
numerators: `32769 = 2^15 + 2^0`, for `k <= 1023`, `(2^k)/32769` rounds
downward to `9006924385222400 * 2^(k-68)`, the exact product with `32769` is
`2^k - 2^(k-60)`, one 128th of the lower ulp below `2^k`, and the final
rounding returns `2^k`; the signed case follows by oddness.  The next
genuinely new odd denominator `65537` is also closed for power-of-two
numerators: `65537 = 2^16 + 2^0`, for `k <= 1023`, `(2^k)/65537` rounds
downward to `9007061817884640 * 2^(k-69)`, the exact product with `65537` is
`2^k - 2^(k-64)`, one 2048th of the lower ulp below `2^k`, and the final
rounding returns `2^k`; the signed case follows by oddness.  The next
genuinely new odd denominator `131073` is also closed for power-of-two
numerators: `131073 = 2^17 + 2^0`, for `k <= 1023`, `(2^k)/131073` rounds
downward to `9007130535788540 * 2^(k-70)`, the exact product with `131073` is
`2^k - 2^(k-68)`, one 32768th of the lower ulp below `2^k`, and the final
rounding returns `2^k`; the signed case follows by oddness.  The next
genuinely new odd denominator `262145` is also closed for power-of-two
numerators: `262145 = 2^18 + 2^0`, for `k <= 1022`, `(2^k)/262145` rounds
upward to `9007164895133696 * 2^(k-71)`, the exact product with `262145` is
`2^k + 2^(k-54)`, one quarter of the upper ulp above `2^k`, and the final
rounding returns `2^k`; the signed case follows by oddness.  The next
genuinely new odd denominator `524289` is also closed for power-of-two
numerators: `524289 = 2^19 + 2^0`, for `k <= 1022`, `(2^k)/524289` rounds
upward to `9007182074904576 * 2^(k-72)`, the exact product with `524289` is
`2^k + 2^(k-57)`, one 32nd of the upper ulp above `2^k`, and the final
rounding returns `2^k`; the signed case follows by oddness.  The next
genuinely new odd denominator `1048577` is also closed for power-of-two
numerators: `1048577 = 2^20 + 2^0`, for `k <= 1022`, `(2^k)/1048577` rounds
upward to `9007190664814592 * 2^(k-73)`, the exact product with `1048577` is
`2^k + 2^(k-60)`, one 256th of the upper ulp above `2^k`, and the final
rounding returns `2^k`; the signed case follows by oddness.  The next
genuinely new odd denominator `2097153` is also closed for power-of-two
numerators: `2097153 = 2^21 + 2^0`, for `k <= 1022`, `(2^k)/2097153` rounds
upward to `9007194959775744 * 2^(k-74)`, the exact product with `2097153` is
`2^k + 2^(k-63)`, one 2048th of the upper ulp above `2^k`, and the final
rounding returns `2^k`; the signed case follows by oddness.  The next
genuinely new odd denominator `4194305` is also closed for power-of-two
numerators: `4194305 = 2^22 + 2^0`, for `k <= 1022`, `(2^k)/4194305` rounds
upward to `9007197107257856 * 2^(k-75)`, the exact product with `4194305` is
`2^k + 2^(k-66)`, one 16384th of the upper ulp above `2^k`, and the final
rounding returns `2^k`; the signed case follows by oddness.  The next
genuinely new odd denominator `8388609` is also closed for power-of-two
numerators: `8388609 = 2^23 + 2^0`, for `k <= 1022`, `(2^k)/8388609` rounds
upward to `9007198180999296 * 2^(k-76)`, the exact product with `8388609` is
`2^k + 2^(k-69)`, one 131072nd of the upper ulp above `2^k`, and the final
rounding returns `2^k`; the signed case follows by oddness.  The next
genuinely new odd denominator `16777217` is also closed for power-of-two
numerators: `16777217 = 2^24 + 2^0`, for `k <= 1022`, `(2^k)/16777217`
rounds upward to `9007198717870112 * 2^(k-77)`, the exact product with
`16777217` is `2^k + 2^(k-72)`, one 1048576th of the upper ulp above `2^k`,
and the final rounding returns `2^k`; the signed case follows by oddness.  The next
genuinely new odd denominator `33554433` is also closed for power-of-two
numerators: `33554433 = 2^25 + 2^0`, for `k <= 1022`, `(2^k)/33554433`
rounds upward to `9007198986305544 * 2^(k-78)`, the exact product with
`33554433` is `2^k + 2^(k-75)`, one 8388608th of the upper ulp above `2^k`,
and the final rounding returns `2^k`; the signed case follows by oddness.  The next
genuinely new odd denominator `67108865` is also closed for power-of-two
numerators: `67108865 = 2^26 + 2^0`, for `k <= 1022`, `(2^k)/67108865`
rounds upward to `9007199120523266 * 2^(k-79)`, the exact product with
`67108865` is `2^k + 2^(k-78)`, one 67108864th of the upper ulp above `2^k`,
and the final rounding returns `2^k`; the signed case follows by oddness.  The next
genuinely new odd denominator `134217729` is also closed for power-of-two
numerators: `134217729 = 2^27 + 2^0`, for `k <= 1022`, `(2^k)/134217729`
rounds downward to `9007199187632128 * 2^(k-80)`, the exact product with
`134217729` is the midpoint `2^k - 2^(k-54)`, and the final tie-to-even step
returns `2^k`; the signed case follows by oddness.  The next
genuinely new odd denominator `268435457` is also closed for power-of-two
numerators: `268435457 = 2^28 + 2^0`, for `k <= 1022`, `(2^k)/268435457`
rounds downward to `9007199221186560 * 2^(k-81)`, the exact product with
`268435457` is `2^k - 2^(k-56)`, and the final one-sixteenth-ulp-below step
returns `2^k`; the signed case follows by oddness.  The next
genuinely new odd denominator `536870913` is also closed for power-of-two
numerators: `536870913 = 2^29 + 2^0`, for `k <= 1022`, `(2^k)/536870913`
rounds downward to `9007199237963776 * 2^(k-82)`, the exact product with
`536870913` is `2^k - 2^(k-58)`, and the new one-sixty-fourth-ulp-below step
returns `2^k`; the signed case follows by oddness.  The next
genuinely new odd denominator `1073741825` is also closed for power-of-two
numerators: `1073741825 = 2^30 + 2^0`, for `k <= 1022`, `(2^k)/1073741825`
rounds downward to `9007199246352384 * 2^(k-83)`, the exact product with
`1073741825` is `2^k - 2^(k-60)`, and the existing one-256th-ulp-below step
returns `2^k`; the signed case follows by oddness.  The next
genuinely new odd denominator `2147483649` is also closed for power-of-two
numerators: `2147483649 = 2^31 + 2^0`, for `k <= 1022`,
`(2^k)/2147483649` rounds downward to
`9007199250546688 * 2^(k-84)`, the exact product with `2147483649` is
`2^k - 2^(k-62)`, and the new one-1024th-ulp-below step returns `2^k`; the
signed case follows by oddness.  The next
genuinely new odd denominator `4294967297` is also closed for power-of-two
numerators: `4294967297 = 2^32 + 2^0`, for `k <= 1022`,
`(2^k)/4294967297` rounds downward to
`9007199252643840 * 2^(k-85)`, the exact product with `4294967297` is
`2^k - 2^(k-64)`, and the existing one-4096th-ulp-below step returns `2^k`;
the signed case follows by oddness.  The next
genuinely new odd denominator `8589934593` is also closed for power-of-two
numerators: `8589934593 = 2^33 + 2^0`, for `k <= 1022`,
`(2^k)/8589934593` rounds downward to
`9007199253692416 * 2^(k-86)`, the exact product with `8589934593` is
`2^k - 2^(k-66)`, and the new one-16384th-ulp-below step returns `2^k`;
the signed case follows by oddness.  The next
genuinely new odd denominator `17179869185` is also closed for power-of-two
numerators: `17179869185 = 2^34 + 2^0`, for `k <= 1022`,
`(2^k)/17179869185` rounds downward to
`9007199254216704 * 2^(k-87)`, the exact product with `17179869185` is
`2^k - 2^(k-68)`, and the existing one-65536th-ulp-below step returns `2^k`;
the signed case follows by oddness.  The next
genuinely new odd denominator `34359738369` is also closed for power-of-two
numerators: `34359738369 = 2^35 + 2^0`, for `k <= 1022`,
`(2^k)/34359738369` rounds downward to
`9007199254478848 * 2^(k-88)`, the exact product with `34359738369` is
`2^k - 2^(k-70)`, and the new one-262144th-ulp-below step returns `2^k`;
the signed case follows by oddness.  The next
genuinely new odd denominator `68719476737` is also closed for power-of-two
numerators: `68719476737 = 2^36 + 2^0`, for `k <= 1022`,
`(2^k)/68719476737` rounds downward to
`9007199254609920 * 2^(k-89)`, the exact product with `68719476737` is
`2^k - 2^(k-72)`, and the new one-1048576th-ulp-below step returns `2^k`;
the signed case follows by oddness.  The next
genuinely new odd denominator `137438953473` is also closed for power-of-two
numerators: `137438953473 = 2^37 + 2^0`, for `k <= 1022`,
`(2^k)/137438953473` rounds downward to
`9007199254675456 * 2^(k-90)`, the exact product with `137438953473` is
`2^k - 2^(k-74)`, and the new one-4194304th-ulp-below step returns `2^k`;
the signed case follows by oddness.  The next
genuinely new odd denominator `274877906945` is also closed for power-of-two
numerators: `274877906945 = 2^38 + 2^0`, for `k <= 1022`,
`(2^k)/274877906945` rounds downward to
`9007199254708224 * 2^(k-91)`, the exact product with `274877906945` is
`2^k - 2^(k-76)`, and the new one-16777216th-ulp-below step returns `2^k`;
the signed case follows by oddness.  The next
genuinely new odd denominator `549755813889` is also closed for power-of-two
numerators: `549755813889 = 2^39 + 2^0`, for `k <= 1022`,
`(2^k)/549755813889` rounds downward to
`9007199254724608 * 2^(k-92)`, the exact product with `549755813889` is
`2^k - 2^(k-78)`, and the new one-67108864th-ulp-below step returns `2^k`;
the signed case follows by oddness.  The next
genuinely new odd denominator `1099511627777` is also closed for power-of-two
numerators: `1099511627777 = 2^40 + 2^0`, for `k <= 1022`,
`(2^k)/1099511627777` rounds downward to
`9007199254732800 * 2^(k-93)`, the exact product with `1099511627777` is
`2^k - 2^(k-80)`, and the new one-268435456th-ulp-below step returns `2^k`;
the signed case follows by oddness.  The next
genuinely new odd denominator `2199023255553` is also closed for power-of-two
numerators: `2199023255553 = 2^41 + 2^0`, for `k <= 1022`,
`(2^k)/2199023255553` rounds downward to
`9007199254736896 * 2^(k-94)`, the exact product with `2199023255553` is
`2^k - 2^(k-82)`, and the new one-1073741824th-ulp-below step returns `2^k`;
the signed case follows by oddness.  The next
genuinely new odd denominator `4398046511105` is also closed for power-of-two
numerators: `4398046511105 = 2^42 + 2^0`, for `k <= 1022`,
`(2^k)/4398046511105` rounds downward to
`9007199254738944 * 2^(k-95)`, the exact product with `4398046511105` is
`2^k - 2^(k-84)`, and the new one-4294967296th-ulp-below step returns `2^k`;
the signed case follows by oddness.  The next
genuinely new odd denominator `8796093022209` is also closed for power-of-two
numerators: `8796093022209 = 2^43 + 2^0`, for `k <= 1022`,
`(2^k)/8796093022209` rounds downward to
`9007199254739968 * 2^(k-96)`, the exact product with `8796093022209` is
`2^k - 2^(k-86)`, and the new one-17179869184th-ulp-below step returns `2^k`;
the signed case follows by oddness.  The next
genuinely new odd denominator `17592186044417` is also closed for power-of-two
numerators: `17592186044417 = 2^44 + 2^0`, for `k <= 1022`,
`(2^k)/17592186044417` rounds downward to
`9007199254740480 * 2^(k-97)`, the exact product with `17592186044417` is
`2^k - 2^(k-88)`, and the new one-68719476736th-ulp-below step returns `2^k`;
the signed case follows by oddness.  The next
genuinely new odd denominator `35184372088833` is also closed for power-of-two
numerators: `35184372088833 = 2^45 + 2^0`, for `k <= 1022`,
`(2^k)/35184372088833` rounds downward to
`9007199254740736 * 2^(k-98)`, the exact product with `35184372088833` is
`2^k - 2^(k-90)`, and the new one-274877906944th-ulp-below step returns `2^k`;
the signed case follows by oddness.  The next
genuinely new odd denominator `70368744177665` is also closed for power-of-two
numerators: `70368744177665 = 2^46 + 2^0`, for `k <= 1022`,
`(2^k)/70368744177665` rounds downward to
`9007199254740864 * 2^(k-99)`, the exact product with `70368744177665` is
`2^k - 2^(k-92)`, and the new one-1099511627776th-ulp-below step returns
`2^k`; the signed case follows by oddness.  The next
genuinely new odd denominator `140737488355329` is also closed for power-of-two
numerators: `140737488355329 = 2^47 + 2^0`, for `k <= 1022`,
`(2^k)/140737488355329` rounds downward to
`9007199254740928 * 2^(k-100)`, the exact product with `140737488355329` is
`2^k - 2^(k-94)`, and the new one-4398046511104th-ulp-below step returns
`2^k`; the signed case follows by oddness.  The next
genuinely new odd denominator `281474976710657` is also closed for power-of-two
numerators: `281474976710657 = 2^48 + 2^0`, for `k <= 1022`,
`(2^k)/281474976710657` rounds downward to
`9007199254740960 * 2^(k-101)`, the exact product with `281474976710657` is
`2^k - 2^(k-96)`, and the new one-17592186044416th-ulp-below step returns
`2^k`; the signed case follows by oddness.  The next
genuinely new odd denominator `562949953421313` is also closed for power-of-two
numerators: `562949953421313 = 2^49 + 2^0`, for `k <= 1022`,
`(2^k)/562949953421313` rounds downward to
`9007199254740976 * 2^(k-102)`, the exact product with `562949953421313` is
`2^k - 2^(k-98)`, and the new one-70368744177664th-ulp-below step returns
`2^k`; the signed case follows by oddness.  The next
genuinely new odd denominator `1125899906842625` is also closed for power-of-two
numerators: `1125899906842625 = 2^50 + 2^0`, for `k <= 1022`,
`(2^k)/1125899906842625` rounds downward to
`9007199254740984 * 2^(k-103)`, the exact product with `1125899906842625` is
`2^k - 2^(k-100)`, and the new one-281474976710656th-ulp-below step returns
`2^k`; the signed case follows by oddness.  The next
genuinely new odd denominator `2251799813685249` is also closed for power-of-two
numerators: `2251799813685249 = 2^51 + 2^0`, for `k <= 1022`,
`(2^k)/2251799813685249` rounds downward to
`9007199254740988 * 2^(k-104)`, the exact product with `2251799813685249` is
`2^k - 2^(k-102)`, and the new one-1125899906842624th-ulp-below step returns
`2^k`; the signed case follows by oddness.  The next
genuinely new odd denominator `4503599627370497` is also closed for power-of-two
numerators: `4503599627370497 = 2^52 + 2^0`, for `k <= 1022`,
`(2^k)/4503599627370497` rounds downward to
`9007199254740990 * 2^(k-105)`, the exact product with `4503599627370497` is
`2^k - 2^(k-104)`, and the new one-4503599627370496th-ulp-below step returns
`2^k`; the signed case follows by oddness.  The next
genuinely new odd denominator `9007199254740993` is also closed for power-of-two
numerators: `9007199254740993 = 2^53 + 2^0`, for `k <= 1022`,
`(2^k)/9007199254740993` rounds downward to
`9007199254740991 * 2^(k-106)`, the exact product with `9007199254740993` is
`2^k - 2^(k-106)`, and the new one-18014398509481984th-ulp-below step returns
`2^k`; the signed case follows by oddness.  The next
genuinely new odd denominator `18014398509481985` is also closed for
power-of-two numerators: `18014398509481985 = 2^54 + 2^0`, for `k <= 1022`,
`(2^k)/18014398509481985` rounds upward to
`9007199254740992 * 2^(k-107)`, the exact product with `18014398509481985` is
`2^k + 2^(k-54)`, and the existing quarter-ulp-above step returns `2^k`; the
signed case follows by oddness.  The next
genuinely new odd denominator `36028797018963969` is also closed for
power-of-two numerators: `36028797018963969 = 2^55 + 2^0`, for `k <= 1022`,
`(2^k)/36028797018963969` rounds upward to
`9007199254740992 * 2^(k-108)`, the exact product with `36028797018963969` is
`2^k + 2^(k-55)`, and the existing one-eighth-ulp-above step returns `2^k`; the
signed case follows by oddness.  The next
genuinely new odd denominator `72057594037927937` is also closed for
power-of-two numerators: `72057594037927937 = 2^56 + 2^0`, for `k <= 1022`,
`(2^k)/72057594037927937` rounds upward to
`9007199254740992 * 2^(k-109)`, the exact product with `72057594037927937` is
`2^k + 2^(k-56)`, and the existing one-sixteenth-ulp-above step returns `2^k`; the
signed case follows by oddness.  The next
genuinely new odd denominator `144115188075855873` is also closed for
power-of-two numerators: `144115188075855873 = 2^57 + 2^0`, for `k <= 1022`,
`(2^k)/144115188075855873` rounds upward to
`9007199254740992 * 2^(k-110)`, the exact product with `144115188075855873` is
`2^k + 2^(k-57)`, and the existing one-thirtysecond-ulp-above step returns `2^k`;
the signed case follows by oddness.  The next
genuinely new odd denominator `288230376151711745` is also closed for
power-of-two numerators: `288230376151711745 = 2^58 + 2^0`, for `k <= 1022`,
`(2^k)/288230376151711745` rounds upward to
`9007199254740992 * 2^(k-111)`, the exact product with `288230376151711745` is
`2^k + 2^(k-58)`, and the new one-sixty-fourth-ulp-above step returns `2^k`;
the signed case follows by oddness.  The next
genuinely new odd denominator `576460752303423489` is also closed for
power-of-two numerators: `576460752303423489 = 2^59 + 2^0`, for `k <= 1022`,
`(2^k)/576460752303423489` rounds upward to
`9007199254740992 * 2^(k-112)`, the exact product with `576460752303423489` is
`2^k + 2^(k-59)`, and the new one-128th-ulp-above step returns `2^k`;
the signed case follows by oddness.  The next
genuinely new odd denominator `1152921504606846977` is also closed for
power-of-two numerators: `1152921504606846977 = 2^60 + 2^0`, for `k <= 1022`,
`(2^k)/1152921504606846977` rounds upward to
`9007199254740992 * 2^(k-113)`, the exact product with `1152921504606846977` is
`2^k + 2^(k-60)`, and the existing one-256th-ulp-above step returns `2^k`;
the signed case follows by oddness.  The next
genuinely new odd denominator `2305843009213693953` is also closed for
power-of-two numerators: `2305843009213693953 = 2^61 + 2^0`, for `k <= 1022`,
`(2^k)/2305843009213693953` rounds upward to
`9007199254740992 * 2^(k-114)`, the exact product with `2305843009213693953` is
`2^k + 2^(k-61)`, and the new one-512th-ulp-above step returns `2^k`;
the signed case follows by oddness.  The next
genuinely new odd denominator `4611686018427387905` is also closed for
power-of-two numerators: `4611686018427387905 = 2^62 + 2^0`, for `k <= 1022`,
`(2^k)/4611686018427387905` rounds upward to
`9007199254740992 * 2^(k-115)`, the exact product with `4611686018427387905` is
`2^k + 2^(k-62)`, and the new one-1024th-ulp-above step returns `2^k`;
the signed case follows by oddness.  The next
genuinely new odd denominator `9223372036854775809` is also closed for
power-of-two numerators: `9223372036854775809 = 2^63 + 2^0`, for `k <= 1022`,
`(2^k)/9223372036854775809` rounds upward to
`9007199254740992 * 2^(k-116)`, the exact product with `9223372036854775809` is
`2^k + 2^(k-63)`, and the existing one-2048th-ulp-above step returns `2^k`;
the signed case follows by oddness.  The next
genuinely new odd denominator `18446744073709551617` is also closed for
power-of-two numerators: `18446744073709551617 = 2^64 + 2^0`, for `k <= 1022`,
`(2^k)/18446744073709551617` rounds upward to
`9007199254740992 * 2^(k-117)`, the exact product with `18446744073709551617` is
`2^k + 2^(k-64)`, and the new one-4096th-ulp-above step returns `2^k`;
the signed case follows by oddness.  The next
genuinely new odd denominator `36893488147419103233` is also closed for
power-of-two numerators: `36893488147419103233 = 2^65 + 2^0`, for `k <= 1022`,
`(2^k)/36893488147419103233` rounds upward to
`9007199254740992 * 2^(k-118)`, the exact product with `36893488147419103233` is
`2^k + 2^(k-65)`, and the existing one-8192nd-ulp-above step returns `2^k`;
the signed case follows by oddness.  The next
genuinely new odd denominator `73786976294838206465` is also closed for
power-of-two numerators: `73786976294838206465 = 2^66 + 2^0`, for `k <= 1022`,
`(2^k)/73786976294838206465` rounds upward to
`9007199254740992 * 2^(k-119)`, the exact product with `73786976294838206465` is
`2^k + 2^(k-66)`, and the existing one-16384th-ulp-above step returns `2^k`;
the signed case follows by oddness.  The next
genuinely new odd denominator `147573952589676412929` is also closed for
power-of-two numerators: `147573952589676412929 = 2^67 + 2^0`, for `k <= 1022`,
`(2^k)/147573952589676412929` rounds upward to
`9007199254740992 * 2^(k-120)`, the exact product with `147573952589676412929`
is `2^k + 2^(k-67)`, and the new one-32768th-ulp-above step returns `2^k`;
the signed case follows by oddness.  The next
genuinely new odd denominator `295147905179352825857` is also closed for
power-of-two numerators: `295147905179352825857 = 2^68 + 2^0`, for `k <= 1022`,
`(2^k)/295147905179352825857` rounds upward to
`9007199254740992 * 2^(k-121)`, the exact product with `295147905179352825857`
is `2^k + 2^(k-68)`, and the new one-65536th-ulp-above step returns `2^k`;
the signed case follows by oddness.  The next
genuinely new odd denominator `590295810358705651713` is also closed for
power-of-two numerators: `590295810358705651713 = 2^69 + 2^0`, for `k <= 1022`,
`(2^k)/590295810358705651713` rounds upward to
`9007199254740992 * 2^(k-122)`, the exact product with `590295810358705651713`
is `2^k + 2^(k-69)`, and the existing one-131072nd-ulp-above step returns `2^k`;
the signed case follows by oddness.  The next
genuinely new odd denominator `1180591620717411303425` is also closed for
power-of-two numerators: `1180591620717411303425 = 2^70 + 2^0`, for `k <= 1022`,
`(2^k)/1180591620717411303425` rounds upward to
`9007199254740992 * 2^(k-123)`, the exact product with `1180591620717411303425`
is `2^k + 2^(k-70)`, and the new one-262144th-ulp-above step returns `2^k`;
the signed case follows by oddness.  The next
genuinely new odd denominator `2361183241434822606849` is also closed for
power-of-two numerators: `2361183241434822606849 = 2^71 + 2^0`, for `k <= 1022`,
`(2^k)/2361183241434822606849` rounds upward to
`9007199254740992 * 2^(k-124)`, the exact product with `2361183241434822606849`
is `2^k + 2^(k-71)`, and the new one-524288th-ulp-above step returns `2^k`;
the signed case follows by oddness.  The next
genuinely new odd denominator `4722366482869645213697` is also closed for
power-of-two numerators: `4722366482869645213697 = 2^72 + 2^0`, for `k <= 1022`,
`(2^k)/4722366482869645213697` rounds upward to
`9007199254740992 * 2^(k-125)`, the exact product with `4722366482869645213697`
is `2^k + 2^(k-72)`, and the existing one-1048576th-ulp-above step returns `2^k`;
the signed case follows by oddness.  The next
genuinely new odd denominator `9444732965739290427393` is also closed for
power-of-two numerators: `9444732965739290427393 = 2^73 + 2^0`, for `k <= 1022`,
`(2^k)/9444732965739290427393` rounds upward to
`9007199254740992 * 2^(k-126)`, the exact product with `9444732965739290427393`
is `2^k + 2^(k-73)`, and the new one-2097152nd-ulp-above step returns `2^k`;
the signed case follows by oddness.  The next
genuinely new odd denominator `18889465931478580854785` is also closed for
power-of-two numerators: `18889465931478580854785 = 2^74 + 2^0`, for `k <= 1022`,
`(2^k)/18889465931478580854785` rounds upward to
`9007199254740992 * 2^(k-127)`, the exact product with `18889465931478580854785`
is `2^k + 2^(k-74)`, and the new one-4194304th-ulp-above step returns `2^k`;
the signed case follows by oddness.  The next
genuinely new odd denominator `37778931862957161709569` is also closed for
power-of-two numerators: `37778931862957161709569 = 2^75 + 2^0`, for `k <= 1022`,
`(2^k)/37778931862957161709569` rounds upward to
`9007199254740992 * 2^(k-128)`, the exact product with `37778931862957161709569`
is `2^k + 2^(k-75)`, and the existing one-8388608th-ulp-above step returns `2^k`;
the signed case follows by oddness.  The next
genuinely new odd denominator `75557863725914323419137` is also closed for
power-of-two numerators: `75557863725914323419137 = 2^76 + 2^0`, for `k <= 1022`,
`(2^k)/75557863725914323419137` rounds upward to
`9007199254740992 * 2^(k-129)`, the exact product with `75557863725914323419137`
is `2^k + 2^(k-76)`, and the new one-16777216th-ulp-above step returns `2^k`;
the signed case follows by oddness.  The next
genuinely new odd denominator `151115727451828646838273` is also closed for
power-of-two numerators: `151115727451828646838273 = 2^77 + 2^0`, for `k <= 1022`,
`(2^k)/151115727451828646838273` rounds upward to
`9007199254740992 * 2^(k-130)`, the exact product with `151115727451828646838273`
is `2^k + 2^(k-77)`, and the new one-33554432nd-ulp-above step returns `2^k`;
the signed case follows by oddness.  The next
genuinely new odd denominator `302231454903657293676545` is also closed for
power-of-two numerators: `302231454903657293676545 = 2^78 + 2^0`, for `k <= 1022`,
`(2^k)/302231454903657293676545` rounds upward to
`9007199254740992 * 2^(k-131)`, the exact product with `302231454903657293676545`
is `2^k + 2^(k-78)`, and the existing one-67108864th-ulp-above step returns `2^k`;
the signed case follows by oddness.  The next source-prefix denominator is also
closed for shifted power-of-two numerators: for `n = 6` and `k <= 1022`,
`(2^(k+1))/6` reuses the denominator-`3` rounded quotient for `(2^k)/3`, the
exact product with `6` is the midpoint `2^(k+1) - 2^((k+1)-54)`, and the final
tie-to-even step returns `2^(k+1)`, with the signed case by oddness.  The
leftover numerator-`1` case for the same denominator is now closed too:
`1/6` rounds downward to `6004799503160661 * 2^-55`, the exact product with
`6` is the midpoint `1 - 2^-54`, and the final tie-to-even step returns `1`;
the signed case follows by oddness and ties to `-1`.  The next displayed
denominator `10` is closed for numerator `m = +/-1`: `10 = 2^3 + 2^1`,
`1/10` rounds upward to `7205759403792794 * 2^-56`, the exact product with
`10` is `1 + 2^-54`, and the final rounding returns `1`; the signed case
again follows by oddness.  The shifted power-of-two denominator-`10` family is
also closed: for `k <= 1021`, `(2^(k+1))/10` reuses the denominator-`5`
rounded quotient for `(2^k)/5`, the exact product with `10` is
`2^(k+1) + 2^((k+1)-54)`, and the final quarter-ulp step returns `2^(k+1)`;
the signed case follows by oddness.  The displayed denominator `12` is closed
for shifted power-of-two numerators too: for `k <= 1021`, `(2^(k+2))/12`
reuses the denominator-`3` rounded quotient for `(2^k)/3`, the exact product
with `12` is the midpoint `2^(k+2) - 2^((k+2)-54)`, and the final tie-to-even
step returns `2^(k+2)`, again with the signed case by oddness.  The displayed
denominator `18` is now closed for shifted power-of-two numerators on the
denominator-`9` route: `18 = 2^4 + 2^1`, for `k <= 1022`,
`(2^(k+1))/18` reuses the rounded quotient for `(2^k)/9`, the exact product
with `18` is the midpoint `2^(k+1) - 2^((k+1)-54)`, and the final tie-to-even
step returns `2^(k+1)`, with the signed case by oddness.  The displayed
denominator `20` is now closed for shifted power-of-two numerators on
the denominator-`5` route: `20 = 2^4 + 2^2`, for `k <= 1020`,
`(2^(k+2))/20` reuses the rounded quotient for `(2^k)/5`, the exact product
with `20` is `2^(k+2) + 2^((k+2)-54)`, and the final quarter-ulp step returns
`2^(k+2)`, with the signed case by oddness.  The broader quoted Kahan theorem work is archived as optional theorem-work history, not an active Chapter 2 audit gate unless explicitly reopened.  Existing finite-selector traces remain as optional mathematical artifacts; the active Problem 2.10 exercise closure is the empirical-source-output classification below.
The book's separate instruction to "Test the theorem on your computer" is
classified as empirical-source-output rather than as a theorem obligation; the
advisory local replay is `experiments/chapter02/problem2_10_kahan_test.py`.

Chapter 2 empirical leading-digit investigation (Problem 2.11):
`problem2_11EmpiricalSource`, `problem2_11_decimalLeadingDigit`,
`problem2_11_decimalLeadingDigit_normalized_bin`,
`problem2_11_decimalLeadingDigit_exists_scaled_mem_one_ten`,
`problem2_11_powerSample`, `problem2_11_factorialSample`,
`problem2_11_powerSample_index_le_1000`,
`problem2_11_powerSample_first`, `problem2_11_powerSample_two_last`,
`problem2_11_powerSample_three_last`,
`problem2_11_factorialSample_index_between`,
`problem2_11_factorialSample_first`, `problem2_11_factorialSample_last`,
`problem2_11_digitCount`, `problem2_11_digitFrequency`,
`problem2_11_digitCount_le_sampleSize`,
`problem2_11_digitFrequency_nonneg`, `problem2_11_digitFrequency_le_one`,
`problem2_11_sum_digitCount_eq_sampleSize`,
`problem2_11_sum_digitFrequency_eq_one`,
`problem2_11_empiricalDigitProbability`, and
`problem2_11_empiricalDigitProbability_prob_eq_frequency`, and
`problem2_11_empiricalDigitProbability_prob_le_one`.  This formalizes
the finite empirical histogram used by the exercise: classified sample counts
over decimal leading digits `1, ..., 9` are bounded by the sample size, sum to
the sample size, and the normalized frequencies lie in `[0,1]` and form a
finite probability distribution.  The generated
source samples `2^n`, `3^n` for `n = 0:1000` and `n!` for `n = 1:1000` are
named with cardinality, endpoint, index-range, and positivity proofs, and any
witnessed decimal leading digit gives the source note's rescaled value in
`[1,10)`.  Actual random-matrix,
physical-constant, and newspaper data are empirical inputs for optional
experiments, not current theorem obligations.

Chapter 2 Edelman reciprocal-product classifier (Problem 2.12):
`FloatingPointFormat.problem2_12_ieeeDouble_predecessor_normalized`,
`FloatingPointFormat.problem2_12_ieeeDouble_one_normalized`,
`FloatingPointFormat.problem2_12_ieeeDouble_rounds_predecessor_to_self`,
`FloatingPointFormat.problem2_12_ieeeDouble_rounds_one_to_self`,
`FloatingPointFormat.problem2_12_ieeeDouble_upper_midpoint_rounds_to_one`,
`FloatingPointFormat.problem2_12_ieeeDouble_rounds_to_predecessor_of_mem_lower_half_cell`,
`FloatingPointFormat.problem2_12_ieeeDouble_rounds_to_one_of_mem_lower_middle_half_cell`,
`FloatingPointFormat.problem2_12_ieeeDouble_rounds_to_one_of_mem_upper_half_cell`,
`FloatingPointFormat.problem2_12_ieeeDouble_final_rounding_options_of_mem_window`,
`FloatingPointFormat.problem2_12_ieeeDouble_reciprocal_finiteNormalRange_of_one_lt_x_lt_two`,
`FloatingPointFormat.problem2_12_ieeeDouble_reciprocal_product_mem_window_of_one_lt_x_lt_two`,
and `FloatingPointFormat.problem2_12_ieeeDouble_reciprocal_product_rounding_options`.
This closes Edelman's result for the repository's finite real-valued
IEEE-double operation wrapper: for every real `x` with `1 < x < 2`, the exact
reciprocal is finite-normal, the product `x * fl(1/x)` lies in
`[1 - 2^-53, 1 + 2^-53]`, and the rounded computation `fl(x * fl(1/x))`
returns either `1 - 2^-53` (`1 - eps/2`) or `1`.  Remaining work is the full
IEEE instruction/special-value/flag semantics and Problem 2.13's smallest
failing `j`.

Chapter 2 Edelman threshold witness (Problem 2.13):
`FloatingPointFormat.problem2_13_candidateJ`,
`FloatingPointFormat.problem2_13_candidateX`,
`FloatingPointFormat.problem2_13_predecessorJ`,
`FloatingPointFormat.problem2_13_predecessorX`,
`FloatingPointFormat.problem2_13_sourceX`,
`FloatingPointFormat.problem2_13_sourceProduct`,
`FloatingPointFormat.problem2_13_reciprocalCellQuotient`,
`FloatingPointFormat.problem2_13_quadraticRemainderQuotient`,
`FloatingPointFormat.problem2_13_reciprocalCellQuotient_remainder_ne_zero_of_pos_lt_candidateJ`,
`FloatingPointFormat.problem2_13_reciprocalCellQuotient_remainder_not_half_of_pos_lt_candidateJ`,
`FloatingPointFormat.problem2_13_reciprocalCellQuotient_remainder_half_trichotomy_of_pos_lt_candidateJ`,
`FloatingPointFormat.problem2_13_quadraticRemainderQuotient_le_29_of_lt_candidateJ`,
`FloatingPointFormat.problem2_13_reciprocalCellQuotient_remainder_eq_quadratic_remainder_of_lt_candidateJ`,
`FloatingPointFormat.problem2_13_reciprocalCellQuotient_remainder_le_threshold_of_quadraticQuotient_eq_29`,
`FloatingPointFormat.problem2_13_reciprocalCellQuotient_remainder_le_threshold_of_quadraticQuotient_le_28_of_left`,
`FloatingPointFormat.problem2_13_reciprocalCellQuotient_normalizedMantissas_of_pos_lt_candidateJ`,
`FloatingPointFormat.problem2_13_sourceX_eq_scaled`,
`FloatingPointFormat.problem2_13_sourceX_candidateJ`,
`FloatingPointFormat.problem2_13_sourceX_predecessorJ`,
`FloatingPointFormat.problem2_13_predecessorJ_succ_eq_candidateJ`,
`FloatingPointFormat.problem2_13_candidateX_sub_predecessorX_eq_ulp`,
`FloatingPointFormat.problem2_13_predecessorX_add_ulp_eq_candidateX`,
`FloatingPointFormat.problem2_13_sourceX_le_sourceX`,
`FloatingPointFormat.problem2_13_sourceX_le_predecessorX_of_lt_candidateJ`,
`FloatingPointFormat.problem2_13_sourceX_lt_candidateX_of_lt_candidateJ`,
`FloatingPointFormat.problem2_13_sourceX_finiteSystem_of_lt_two_pow_52`,
`FloatingPointFormat.problem2_13_sourceX_finiteSystem_of_lt_candidateJ`,
`FloatingPointFormat.problem2_13_candidateX_finiteSystem`,
`FloatingPointFormat.problem2_13_sourceX_between_one_two_of_pos_lt_candidateJ`,
`FloatingPointFormat.problem2_13_sourceX_reciprocal_strict_between_of_scaled_interval`,
`FloatingPointFormat.problem2_13_sourceX_reciprocal_strict_between_of_nat_scaled_interval`,
`FloatingPointFormat.problem2_13_reciprocalCellQuotient_nat_scaled_interval`,
`FloatingPointFormat.problem2_13_sourceX_reciprocal_strict_between_of_quotient_remainder`,
`FloatingPointFormat.problem2_13_reciprocalCellQuotient_midpoint_left_of_twice_remainder_lt`,
`FloatingPointFormat.problem2_13_reciprocalCellQuotient_midpoint_right_of_denominator_lt_twice_remainder`,
`FloatingPointFormat.problem2_13_reciprocalCellQuotient_scaled_product_left_ge_of_remainder_le`,
`FloatingPointFormat.problem2_13_reciprocalCellQuotient_scaled_product_right_ge`,
`FloatingPointFormat.problem2_13_sourceX_reciprocal_left_closer_of_scaled_midpoint`,
`FloatingPointFormat.problem2_13_sourceX_reciprocal_right_closer_of_scaled_midpoint`,
`FloatingPointFormat.problem2_13_sourceX_reciprocal_rounds_to_left_of_adjacent_scaled`,
`FloatingPointFormat.problem2_13_sourceX_reciprocal_rounds_to_right_of_adjacent_scaled`,
`FloatingPointFormat.problem2_13_sourceX_reciprocal_rounds_to_left_of_scaled_interval_midpoint`,
`FloatingPointFormat.problem2_13_sourceX_reciprocal_rounds_to_right_of_scaled_interval_midpoint`,
`FloatingPointFormat.problem2_13_sourceX_reciprocal_rounds_to_left_of_nat_interval_midpoint`,
`FloatingPointFormat.problem2_13_sourceX_reciprocal_rounds_to_right_of_nat_interval_midpoint`,
`FloatingPointFormat.problem2_13_sourceX_reciprocal_rounds_to_left_of_quotient_midpoint`,
`FloatingPointFormat.problem2_13_sourceX_reciprocal_rounds_to_right_of_quotient_midpoint`,
`FloatingPointFormat.problem2_13_sourceX_reciprocal_rounds_to_left_of_quotient_midpoint_of_pos_lt_candidateJ`,
`FloatingPointFormat.problem2_13_sourceX_reciprocal_rounds_to_right_of_quotient_midpoint_of_pos_lt_candidateJ`,
`FloatingPointFormat.problem2_13_sourceX_reciprocal_rounds_to_left_of_quotient_remainder_lt_half`,
`FloatingPointFormat.problem2_13_sourceX_reciprocal_rounds_to_right_of_quotient_remainder_gt_half`,
`FloatingPointFormat.problem2_13_sourceX_rounding_options_of_pos_lt_candidateJ`,
`FloatingPointFormat.problem2_13_sourceProduct_mem_window_of_pos_lt_candidateJ`,
`FloatingPointFormat.problem2_13_sourceProduct_eq_scaled_of_reciprocal_rounds`,
`FloatingPointFormat.problem2_13_sourceProduct_lower_midpoint_le_of_scaled_product_ge`,
`FloatingPointFormat.problem2_13_sourceProduct_lt_lower_midpoint_of_scaled_product_lt`,
`FloatingPointFormat.problem2_13_sourceX_rounds_to_predecessor_of_sourceProduct_lt_lower_midpoint`,
`FloatingPointFormat.problem2_13_sourceX_rounds_to_one_of_lower_midpoint_le`,
`FloatingPointFormat.problem2_13_sourceX_rounds_to_one_iff_lower_midpoint_le`,
`FloatingPointFormat.problem2_13_sourceX_rounds_to_one_of_reciprocal_scaled_product_ge`,
`FloatingPointFormat.problem2_13_sourceX_rounds_to_predecessor_of_reciprocal_scaled_product_lt`,
`FloatingPointFormat.problem2_13_sourceX_rounds_to_one_iff_reciprocal_scaled_product_ge`,
`FloatingPointFormat.problem2_13_sourceX_rounds_to_one_of_left_reciprocal_nat_certificate`,
`FloatingPointFormat.problem2_13_sourceX_rounds_to_one_of_right_reciprocal_nat_certificate`,
`FloatingPointFormat.problem2_13_sourceX_rounds_to_predecessor_of_left_reciprocal_nat_certificate`,
`FloatingPointFormat.problem2_13_sourceX_rounds_to_predecessor_of_right_reciprocal_nat_certificate`,
`FloatingPointFormat.problem2_13_sourceX_rounds_to_one_of_left_reciprocal_quotient_certificate`,
`FloatingPointFormat.problem2_13_sourceX_rounds_to_one_of_right_reciprocal_quotient_certificate`,
`FloatingPointFormat.problem2_13_sourceX_rounds_to_one_of_left_reciprocal_quotient_integer_certificate`,
`FloatingPointFormat.problem2_13_sourceX_rounds_to_one_of_right_reciprocal_quotient_integer_certificate`,
`FloatingPointFormat.problem2_13_sourceX_rounds_to_one_of_left_reciprocal_quotient_remainder_certificate`,
`FloatingPointFormat.problem2_13_sourceX_rounds_to_one_of_right_reciprocal_quotient_remainder_certificate`,
`FloatingPointFormat.problem2_13_sourceX_rounds_to_one_of_left_reciprocal_quotient_remainder_le_threshold`,
`FloatingPointFormat.problem2_13_sourceX_rounds_to_one_of_left_reciprocal_quotient_remainder_lt_half_le_threshold`,
`FloatingPointFormat.problem2_13_sourceX_rounds_to_one_of_left_reciprocal_quadraticQuotient_eq_29`,
`FloatingPointFormat.problem2_13_sourceX_rounds_to_one_of_left_reciprocal_quadraticQuotient_le_28`,
`FloatingPointFormat.problem2_13_sourceX_rounds_to_one_of_right_reciprocal_quotient_remainder_gt_half`,
`FloatingPointFormat.problem2_13_sourceX_rounds_to_one_of_quadraticQuotient_eq_29`,
`FloatingPointFormat.problem2_13_sourceX_rounds_to_one_of_quadraticQuotient_le_28`,
`FloatingPointFormat.problem2_13_sourceX_rounds_to_one_of_pos_lt_candidateJ`,
`FloatingPointFormat.problem2_13_predecessorX_finiteSystem`,
`FloatingPointFormat.problem2_13_predecessor_candidate_adjacentNormalized`,
`FloatingPointFormat.problem2_13_predecessorX_lt_candidateX`,
`FloatingPointFormat.problem2_13_candidate_reciprocal_rounds_to_lower`,
`FloatingPointFormat.problem2_13_candidate_reciprocal_product_eq`,
`FloatingPointFormat.problem2_13_sourceProduct_candidateJ`,
`FloatingPointFormat.problem2_13_sourceProduct_candidateJ_mem_window`,
`FloatingPointFormat.problem2_13_candidate_sourceProduct_lt_lower_midpoint`,
`FloatingPointFormat.problem2_13_candidate_scaled_product_lt_lower_midpoint_threshold`,
`FloatingPointFormat.problem2_13_candidate_rounds_to_predecessor_of_sourceProduct_lower_midpoint`,
`FloatingPointFormat.problem2_13_candidate_rounds_to_predecessor`, and
`FloatingPointFormat.problem2_13_candidate_rounds_ne_one`, plus the predecessor
theorems `FloatingPointFormat.problem2_13_predecessor_reciprocal_rounds_to_lower`,
`FloatingPointFormat.problem2_13_predecessor_scaled_product_ge_lower_midpoint_threshold`,
`FloatingPointFormat.problem2_13_predecessor_reciprocal_product_eq`,
`FloatingPointFormat.problem2_13_sourceProduct_predecessorJ`,
`FloatingPointFormat.problem2_13_predecessor_sourceProduct_lower_midpoint_le`,
`FloatingPointFormat.problem2_13_predecessor_rounds_to_one_of_sourceProduct_lower_midpoint`,
`FloatingPointFormat.problem2_13_predecessor_rounds_to_one_of_scaled_product_certificate`,
and
`FloatingPointFormat.problem2_13_predecessor_rounds_to_one`.  These name the
source family `x_j = 1 + j*2^-52`, prove the candidate and predecessor are
one source index and one ulp apart, and prove that every source index
`j < 257736490` gives an input no larger than the certified predecessor and
strictly below the failing candidate.  They also prove that every source input
with `j < 2^52`, hence every source input below the candidate index, is a finite
IEEE-double value, and that every positive source index below the candidate lies
in `(1,2)` and has a final rounded reciprocal-product result in the two-cell
set `{1 - 2^-53, 1}`.  The source scaling identity rewrites
`x_j = (2^52 + j)*2^-52`, and the adjacent reciprocal-rounding certificates
show that any real adjacent-cell proof for `1/x_j` between `k*2^-53` and
`(k+1)*2^-53` directly yields the corresponding finite round-to-even reciprocal
endpoint.  The source-product window and midpoint branch theorems show that
selecting the `1` branch for earlier inputs is equivalent to proving
`1 - 2^-54 <= x_j*fl(1/x_j)`.  The scaled-product bridge sharpens that
obligation: if the rounded reciprocal is `k*2^-53`, then Lean rewrites the
source product as `((2^52 + j)*k)*2^-105`, proves that the integer threshold
`2^105 - 2^51` decides the lower-midpoint comparison, and proves for earlier
inputs that the final result is `1` iff
`2^105 - 2^51 <= (2^52 + j)*k`.  They also prove that the candidate
`j = 257736490` is a genuine failing case for the finite real-valued
IEEE-double operation wrapper, that both the candidate input and its predecessor
are finite IEEE-double values, and that the predecessor is the adjacent
IEEE-double input gridpoint below the candidate.  The rounded reciprocal has
mantissa `9007198739268041`, the rounded-reciprocal product is
`1 - 2251799886937606*2^-105`, the candidate scaled product is strictly below
the integer midpoint threshold, and the final rounded value is recovered
through the source-product lower branch as `1 - 2^-53`, not `1`.  They also
prove that the immediately preceding `j = 257736489` has source product
`1 - 2251798855991677*2^-105`, its scaled product is above the integer
threshold, and it still rounds to `1` through both the source-product branch
selector and the scaled-product certificate theorem.  The quotient bridge names
`floor(2^105/(2^52+j))` as the reciprocal-cell mantissa candidate and shows
that every positive earlier source index gives normalized IEEE-double quotient
mantissas for both adjacent reciprocal endpoints.  It also reduces the quotient
midpoint side to comparing `2*((2^105) % (2^52+j))` with `2^52+j`.  A nonzero
quotient remainder is now proved automatically for every `0 < j < 257736490`.
Exact half-remainder ties are also ruled out in that range, so the remainder
comparison splits cleanly into left and right branches.  The remainder-half side
and final scaled-product integer certificates now select the `1` branch; on the
right-half branch the scaled-product certificate is automatic, and on the
left-half branch it reduces to the remainder threshold
`((2^105) % (2^52+j)) <= 2^51`.  The quadratic-remainder quotient
`floor(2*j^2/(2^52+j))` is proved at most `29` below the candidate, the original
remainder is rewritten as `(2*j^2) % (2^52+j)`, and the whole top quotient band
`floor(2*j^2/(2^52+j)) = 29` is proved to round back to `1`.  The lower
quadratic quotient bands `<= 28` are closed by the left-branch threshold
theorem, and the final all-earlier wrapper proves that every positive
`j < 257736490` rounds back to `1`.  Thus Problem 2.13's finite real-valued
IEEE-double operation-wrapper minimality proof is closed: `j = 257736490`
fails, while all positive earlier source indices still return `1`.  The
remaining scope is full IEEE instruction/special-value/flag semantics.

Chapter 2 Kahan unit-roundoff probe (Problem 2.14):
`FloatingPointFormat.problem2_14_ieeeDouble_four_thirds_rounds_to_lower`,
`FloatingPointFormat.problem2_14_ieeeDouble_four_thirds_minus_one`,
`FloatingPointFormat.problem2_14_ieeeDouble_three_mul_four_thirds_minus_one`,
`FloatingPointFormat.problem2_14_ieeeDouble_kahan_probe_error`,
`FloatingPointFormat.problem2_14_ieeeDoubleKahanEstimate_eq_machineEpsilon`,
`FloatingPointFormat.problem2_14_ieeeDoubleKahanEstimate_eq_two_unitRoundoff`,
`FloatingPointFormat.problem2_14_ieeeSingle_four_thirds_rounds_to_upper`,
`FloatingPointFormat.problem2_14_ieeeSingle_four_thirds_minus_one`,
`FloatingPointFormat.problem2_14_ieeeSingle_three_mul_four_thirds_minus_one`,
`FloatingPointFormat.problem2_14_ieeeSingle_kahan_probe_error`,
`FloatingPointFormat.problem2_14_ieeeSingleKahanEstimate_eq_machineEpsilon`,
and `FloatingPointFormat.problem2_14_ieeeSingleKahanEstimate_eq_two_unitRoundoff`.
These prove the finite IEEE-double and IEEE-single round-to-even wrapper traces
for `|3*(4/3 - 1) - 1|`: the double signed probe is `-2^-52`, while the
single signed probe is `2^-23`; in both cases the absolute probe value is
`2 * u`.  This records the source's over-estimate behavior for the modeled
finite wrapper, not a full hardware/IEEE special-value theorem.

Chapter 2 elementary IEEE special probes (Problems 2.15--2.16):
`problem2_15_16Probe`, `problem2_15_16Environment`,
`problem2_15_16ProbeList`, `problem2_15_16ProbeList_length`,
`problem2_15_16ProbeList_nodup`, `problem2_15_16Probe_mem_sourceList`,
`problem2_15_16ReferenceResult`, `problem2_15_16ReferenceEnvironment_eval`,
`problem2_15_reference_zero_pow_zero`,
`problem2_15_16_probe_can_return`,
`problem2_15_16_probe_not_forced_by_core_ieee_model`, and the
`problem2_16_reference_*` theorems.  These record the source probes `0^0`,
`1^inf`, `2^inf`, `exp(inf)`, `exp(-inf)`, `sign(NaN)`, `sign(-NaN)`,
`NaN^0`, `inf^0`, `1^NaN`, and `log(inf)`, `log(-inf)`, `log(0)`.  The named
source list has length `13`, has no duplicates, and contains every formal
probe constructor.  The local reference convention returns common
quiet/default values, while the
under-specification theorem proves that the repository's core IEEE primitive
model does not force a unique elementary-function result.

Chapter 2 largest-finite overflow exercise (Problem 2.17):
`FloatingPointFormat.problem2_17_two_mul_maxFiniteMagnitude_finiteOverflowRange`,
together with the existing `ieeeOverflowValue_*` mode equations, closes the
formal core of the source exercise: the exact value `2*xmax` is in the
source-facing overflow range, and the modeled IEEE overflow-value table shows
that directed rounding toward zero or toward negative infinity returns the
positive largest finite endpoint for this positive overflow input, while
nearest/even and toward positive infinity return positive infinity.  Trap,
flag, and hardware exception details remain in the broader IEEE result layer.

Chapter 2 rounded discriminant sign counterexample (§2.7 FMA discussion):
`problem2_17_discriminant`, `problem2_17_computedDiscriminant`,
`problem2_17_true_discriminant_nonnegative`,
`problem2_17_true_discriminant_eq_one_tenth`,
`problem2_17_computed_discriminant_negative`,
`problem2_17_standard_model_witness_exact_values`,
`problem2_17_standard_model_counterexample`, and
`problem2_17_standard_model_counterexample_with_decimal_finite_inputs`.
These prove that the source's
phenomenon can occur in the standard model for the rounded path
`fl(fl(b*b) - fl(a*c))`: with `a = 1`, `b = 1`, `c = 9/10`, the true
`b^2 - a*c` is `1/10 >= 0`, while a valid model with `u = 1/10` rounds the two
products in opposite directions and returns computed discriminant `-9/100`.
The strengthened witness also proves that `1`, `1`, and `9/10` are finite
values of the concrete one-digit decimal format; the rounded operations are
still supplied by the abstract model, not by a concrete hardware or finite
operation trace.

Chapter 2 exponent-gap strengthening counterexample (Problem 2.18):
`problem2_18_positiveExponentGapAtMostOne`,
`problem2_18_twenty_one_exponent_gap`,
`problem2_18_nineteen_finiteNormalRange`,
`problem2_18_sub_twenty_one_rounds_to_twenty`,
`problem2_18_nineteen_not_finiteSystem`,
`problem2_18_source_counterexample_exact_values`, and
`problem2_18_exponent_gap_not_sufficient_for_exact_subtraction`.  These prove
that positivity plus normalized exponents differing by at most one is not
enough to guarantee exact subtraction: in the one-digit decimal format,
`20` and `1` satisfy the proposed exponent-gap condition and `20-1 = 19` is in
the normal range, but it is not representable and finite round-to-even
subtraction returns `20`.  This refutes the Problem 2.18 strengthening at the
finite selector layer; full hardware/IEEE operation semantics remain separate.

Chapter 2 square-root identity requirements (Problem 2.19):
`FloatingPointFormat.problem2_19_sqrt_square_eq_abs_of_finiteSystem`,
`FloatingPointFormat.problem2_19_roundedSqrtSquare`,
`FloatingPointFormat.problem2_19_decimalOneDigitThreeExponent_sqrt_two_rounds_to_one`,
`FloatingPointFormat.problem2_19_decimalOneDigitThreeExponent_roundedSqrtSquare_two_eq_one`,
`FloatingPointFormat.problem2_19_roundedSqrtSquare_not_abs_counterexample`,
and
`FloatingPointFormat.problem2_19_first_requirement_holds_second_fails`.
These separate the reasonable requirement from the unreasonable one.  For a
finite input `x`, the finite round-to-even square-root wrapper returns `|x|`
exactly on the exact square input `x^2`.  But in the one-digit decimal format,
`fl(sqrt(2)) = 1`, so the rounded-root-then-square path returns `1`, not `|2|`.
Full IEEE special-value/flag semantics remain separate.

Chapter 2 naive norm-ratio counterexample (Problem 2.20):
`problem2_20_exactRatio`, `problem2_20_computedRatio`,
`problem2_20_finiteComputedRatio`,
`problem2_20_exactRatio_abs_le_one`, `problem2_20_exactRatio_le_one`,
`problem2_20_exact_witness_ratio_eq_one`,
`problem2_20_computed_witness_ratio_gt_one`, and
`problem2_20_standard_model_counterexample`, strengthened by
`problem2_20_standard_model_counterexample_with_decimal_finite_inputs`.
The exact-ratio lemmas prove the source Euclidean baseline:
`|x / sqrt(x^2+y^2)| <= 1`, hence `x / sqrt(x^2+y^2) <= 1` for all real
components.  The counterexample theorems prove that the source's phenomenon can
occur in the standard model for
the naive path
`fl(x / flsqrt(fl(fl(x*x) + fl(y*y))))`: with `x = 11/10` and `y = 0`, the
exact real ratio is `1`, while a valid abstract model with `u = 1/5` rounds
the first square down to `1` and computes the final ratio as `11/10 > 1`.
The strengthened witness also proves `11/10` and `0` are finite values of the
local two-digit decimal input format
`FloatingPointFormat.problem2_20_decimalTwoDigitThreeExponentFormat`.
The concrete finite-selector companion is
`FloatingPointFormat.problem2_20_decimalOneDigitThreeExponent_finite_selector_counterexample`:
for `x = 3/2` and `y = 0`,
`problem2_20_exact_three_halves_zero_ratio_eq_one` proves the exact ratio is
`1`, while the one-digit decimal round-to-even operation path rounds
`(3/2)*(3/2)` to `2`, keeps `0*0` and `2+0` exact, uses the Problem 2.19
square-root fact `fl(sqrt(2)) = 1`, and rounds `(3/2)/1` to the even endpoint
`2`.  The audit theorem
`problem2_20_decimalOneDigitThreeExponent_three_halves_not_finiteSystem` proves
that `3/2` is not a finite value of that one-digit format, so this companion is
only a real-input finite-selector trace.  The range audit
`FloatingPointFormat.problem2_20_decimalOneDigitThreeExponent_exact_trace_range_audit`
proves the nonzero exact intermediates are finite-normal, while the exact
`0*0` branch lies in the finite underflow range.  The generic audit predicate
`FloatingPointFormat.problem2_20_noSquareUnderflowInputs` names the two-square
no-underflow side condition, and
`FloatingPointFormat.problem2_20_components_ne_zero_of_noSquareUnderflowInputs`
proves it forces both components to be nonzero.  The theorem
`FloatingPointFormat.problem2_20_decimalOneDigitThreeExponent_trace_exceeds_one_but_fails_source_audit`
packages the current one-digit trace together with the two reasons it cannot
close the source-compliant row: `3/2` is not a finite value of the chosen
format, and the trace fails `problem2_20_noSquareUnderflowInputs` because
`0*0` underflows.  A concrete finite-selector or IEEE instruction trace with
finite inputs, nonzero components, and the source's no-overflow/no-underflow
side condition remains open, along with full IEEE instruction semantics with
flags, traps, and special values.

Chapter 2 naive IEEE maximum branch (Problem 2.21):
`ieeeNaiveMax`, `ieeeNaiveMax_finite_finite_left_of_lt`,
`ieeeNaiveMax_finite_finite_right_of_le`,
`ieeeNaiveMax_finite_finite_eq_max`, `ieeeNaiveMax_left_nan`,
`ieeeNaiveMax_right_nan`, `ieeeNaiveMax_nan_finite`,
`ieeeNaiveMax_finite_nan`, `ieeeNaiveMax_nan_finite_ne_finite_nan`,
`ieeeNaiveMax_left_nan_finite_result_not_nan`,
`ieeeNaiveMax_concrete_nan_counterexample`,
`ieeeNaiveMax_not_nan_propagating`, and
`ieeeNaiveMax_finite_correct_but_not_nan_propagating`.  These formalize the
literal source code
`if x > y then x else y` over the modeled IEEE value/comparison layer.  On
ordinary finite operands the branch computes the real maximum, but modeled IEEE
`>` is false when either operand is NaN, so a left NaN with finite right operand
is discarded, while a right NaN is returned.  Thus the branch is not symmetric
and does not implement a NaN-propagating maximum; the final packaged theorem
states both the finite-input correctness and the NaN-propagation failure.  This
is the Problem 2.21 code-path theorem, not a full IEEE max/min instruction
semantics.

Chapter 2 Kahan Heron guard-digit accuracy (Problem 2.22):
`problem2_22_guard_digit_a_sub_b_exact` and
`problem2_22_kahanHeronArea_relError_le_gamma9_unitRoundoff`.  These expose the
source-shaped theorem surface for Kahan's parenthesized Heron formula: the
`a-b` subtraction is exact under the ordered-side guard-digit/Sterbenz
hypotheses, and the already-formalized finite trace gives relative error at
most `(1 + gamma_9) * (1 + u)^2 - 1` under the listed finite-normal side
conditions.  Remaining scope is a full IEEE/special-value instantiation and any
source variant that removes those concrete range hypotheses.

Chapter 2 guard-digit versus no-guard sequence (Problem 2.23):
`problem2_23_guardDigitY_eq_x_of_finiteSystem`,
`problem2_23_noGuardY_error_formula`,
`problem2_23_binaryNoGuardScaledMantissa_eq_add_mod_two`,
`problem2_23_binaryNoGuardYScaled_error_eq_low_bit`,
`problem2_23_binaryNoGuardYScaled_eq_scaledValue_add_low_bit`, and
`problem2_23_guard_and_binary_noGuard_summary`.  These formalize the
source computation `y = (x+x)-x`: on the finite exact/guard-digit path the
sequence returns `x` when `x` and `x+x` remain finite, while the no-guard model
exposes the four perturbations in the two operation sequence.  At the binary
mantissa level, dropping the guard bit changes the scaled mantissa from `m` to
`m + m % 2`; equivalently, the no-guard scaled value is the original scaled
value plus the dropped low bit times the lattice scale.  Full executable binary
hardware semantics and exceptional cases remain
separate.

Chapter 2 Kahan nonzero expression (Problem 2.24):
`FloatingPointFormat.problem2_24_eval`,
`FloatingPointFormat.problem2_24_y1`,
`FloatingPointFormat.problem2_24_y2`,
`FloatingPointFormat.problem2_24_y3`,
`FloatingPointFormat.problem2_24_eval_eq_rounded_last_sum`,
`FloatingPointFormat.problem2_24_exactExpr`,
`FloatingPointFormat.problem2_24_exactExpr_eq_three_mul_sub_one`,
`FloatingPointFormat.problem2_24_exactExpr_eq_zero_iff`,
`FloatingPointFormat.problem2_24_exactExpr_ne_zero_of_ne_one_third`,
`FloatingPointFormat.problem2_24_eval_eq_last_exact_of_finiteSystem_last_sum`,
`FloatingPointFormat.problem2_24_eval_eq_zero_iff_last_sum_eq_zero_of_finiteSystem_last_sum`,
`FloatingPointFormat.problem2_24_y3_eq_neg_x_of_eval_eq_zero_of_finiteSystem_last_sum`,
`FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_last_sum_of_last_sum_ne_zero`,
`FloatingPointFormat.problem2_24_eval_eq_three_mul_sub_one_of_finiteSystem_intermediates`,
`FloatingPointFormat.problem2_24_eval_eq_exactExpr_of_finiteSystem_intermediates`,
`FloatingPointFormat.problem2_24_eq_one_third_of_eval_eq_zero_of_finiteSystem_intermediates`,
`FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_intermediates_of_ne_one_third`,
`FloatingPointFormat.problem2_24_eval_eq_zero_implies_not_all_finiteSystem_intermediates_of_ne_one_third`,
`FloatingPointFormat.problem2_24_eval_eq_zero_implies_exists_nonfinite_exact_intermediate_of_ne_one_third`,
`FloatingPointFormat.problem2_24_eval_eq_zero_implies_later_nonfinite_exact_intermediate_of_finiteSystem_input_of_ne_one_third`,
`FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_input_of_ne_one_third_of_second_third_exact_intermediates`,
`FloatingPointFormat.problem2_24_eval_eq_zero_implies_second_or_third_nonfinite_exact_intermediate_of_finiteSystem_input_of_ne_one_third`,
`FloatingPointFormat.finiteRoundToEven_eq_zero_abs_le_half_minSubnormalMagnitude_of_subnormalMantissa_one`,
`FloatingPointFormat.finiteSystem_exists_int_mul_minSubnormalMagnitude`,
`FloatingPointFormat.int_mul_minSubnormalMagnitude_abs_ge_of_ne_zero`,
`FloatingPointFormat.finiteSystem_add_eq_zero_of_abs_le_half_minSubnormalMagnitude`,
`FloatingPointFormat.problem2_24_eval_eq_zero_last_sum_abs_le_half_minSubnormalMagnitude`,
`FloatingPointFormat.problem2_24_y1_finiteSystem`,
`FloatingPointFormat.problem2_24_y2_finiteSystem`,
`FloatingPointFormat.problem2_24_y3_finiteSystem`,
`FloatingPointFormat.problem2_24_y1_first_sub_nearestRoundingToFinite`,
`FloatingPointFormat.problem2_24_y1_first_sub_distance_to_x_le_half`,
`FloatingPointFormat.problem2_24_y1_first_sub_distance_to_zero_product_le`,
`FloatingPointFormat.problem2_24_y1_nonneg_of_half_le`,
`FloatingPointFormat.problem2_24_y1_le_two_mul_x_sub_one_of_half_le`,
`FloatingPointFormat.problem2_24_y1_between_zero_and_two_mul_x_sub_one_of_half_le`,
`FloatingPointFormat.problem2_24_y1_nonpos_of_le_half`,
`FloatingPointFormat.problem2_24_two_mul_x_sub_one_le_y1_of_le_half`,
`FloatingPointFormat.problem2_24_y1_between_two_mul_x_sub_one_and_zero_of_le_half`,
`FloatingPointFormat.problem2_24_y1_between_x_sub_one_and_x_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_y2_second_add_nearestRoundingToFinite`,
`FloatingPointFormat.problem2_24_y2_second_add_distance_to_zero_le_self`,
`FloatingPointFormat.problem2_24_y2_second_add_distance_to_zero_product_le`,
`FloatingPointFormat.problem2_24_y2_nonneg_of_y1_add_x_nonneg`,
`FloatingPointFormat.problem2_24_y2_le_two_mul_y1_add_x_of_y1_add_x_nonneg`,
`FloatingPointFormat.problem2_24_y2_between_zero_and_two_mul_y1_add_x_of_y1_add_x_nonneg`,
`FloatingPointFormat.problem2_24_y2_nonpos_of_y1_add_x_nonpos`,
`FloatingPointFormat.problem2_24_two_mul_y1_add_x_le_y2_of_y1_add_x_nonpos`,
`FloatingPointFormat.problem2_24_y2_between_two_mul_y1_add_x_and_zero_of_y1_add_x_nonpos`,
`FloatingPointFormat.problem2_24_y2_second_add_distance_to_y1_le_abs_x`,
`FloatingPointFormat.problem2_24_y2_second_add_distance_to_x_le_abs_y1`,
`FloatingPointFormat.problem2_24_y2_second_add_distance_to_x_product_le_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_eval_eq_zero_last_sum_eq_zero_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_y3_eq_neg_x_of_eval_eq_zero_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_y3_eq_neg_x_last_sub_nearestRoundingToFinite`,
`FloatingPointFormat.problem2_24_y3_eq_neg_x_last_sub_minimal`,
`FloatingPointFormat.problem2_24_y3_eq_neg_x_last_sub_distance_to_y2_le_half`,
`FloatingPointFormat.problem2_24_y3_eq_neg_x_last_sub_distance_to_zero_product_le`,
`FloatingPointFormat.problem2_24_y3_eq_neg_x_last_sub_distance_to_neg_half_product_nonneg`,
`FloatingPointFormat.problem2_24_y3_eq_neg_x_last_sub_y2_bound_of_pos`,
`FloatingPointFormat.problem2_24_y3_eq_neg_x_last_sub_y2_lower_bound_of_lt_half`,
`FloatingPointFormat.problem2_24_eval_eq_zero_last_sub_minimal_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_eval_eq_zero_last_sub_distance_to_y2_le_half_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_eval_eq_zero_last_sub_distance_to_zero_product_le_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_eval_eq_zero_last_sub_y2_bound_of_pos_finiteSystem_input`,
`FloatingPointFormat.problem2_24_eval_eq_zero_last_sub_y2_lower_bound_of_lt_half_finiteSystem_input`,
`FloatingPointFormat.problem2_24_eval_eq_zero_y2_pos_of_lt_half_finiteSystem_input`,
`FloatingPointFormat.problem2_24_eval_eq_zero_y1_add_x_pos_of_lt_half_finiteSystem_input`,
`FloatingPointFormat.problem2_24_eval_eq_zero_y2_add_x_between_zero_and_one_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_eval_eq_zero_input_nonneg_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_eval_eq_zero_input_le_one_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_eval_eq_zero_input_mem_unit_interval_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_input_of_half_le`,
`FloatingPointFormat.problem2_24_eval_zero_ne_zero_of_half_and_one_finiteSystem`,
`FloatingPointFormat.problem2_24_eval_eq_zero_input_pos_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_eval_eq_zero_input_mem_open_lower_half_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_eval_eq_zero_input_mem_tenth_to_half_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_y1_first_sub_distance_to_neg_x_product_nonneg_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_y1_le_three_mul_x_sub_one_of_y1_add_x_pos_finiteSystem_input`,
`FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_input_of_lt_one_six`,
`FloatingPointFormat.problem2_24_eval_eq_zero_input_ge_one_six_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_eval_eq_zero_input_mem_one_six_to_half_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_input_of_lt_nine_thirty_four`,
`FloatingPointFormat.problem2_24_eval_eq_zero_input_ge_nine_thirty_four_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_eval_eq_zero_input_mem_nine_thirty_four_to_half_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_y1_eq_x_sub_half_of_finiteSystem_input_of_quarter_lt_of_lt_one`,
`FloatingPointFormat.problem2_24_first_exact_intermediate_finiteSystem_of_quarter_lt_of_lt_one`,
`FloatingPointFormat.problem2_24_eval_eq_zero_first_exact_intermediate_finiteSystem_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_second_exact_intermediate_finiteSystem_of_quarter_lt_of_lt_one_third`,
`FloatingPointFormat.problem2_24_eval_eq_zero_second_exact_intermediate_finiteSystem_of_finiteSystem_input_of_lt_one_third`,
`FloatingPointFormat.problem2_24_eval_eq_zero_implies_last_two_nonfinite_exact_intermediate_of_finiteSystem_input_of_lt_one_third`,
`FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_input_of_lt_one_third_of_third_exact_intermediate_finiteSystem`,
`FloatingPointFormat.problem2_24_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_finiteSystem_input_of_lt_one_third`,
`FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_input_of_lt_five_eighteen`,
`FloatingPointFormat.problem2_24_eval_eq_zero_input_ge_five_eighteen_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_eval_eq_zero_input_mem_five_eighteen_to_half_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_y3_eq_neg_x_last_sub_distance_to_y1_product_nonneg`,
`FloatingPointFormat.problem2_24_y3_eq_neg_x_last_sub_y2_y1_bound_of_y1_add_x_pos`,
`FloatingPointFormat.problem2_24_eval_eq_zero_last_sub_y2_y1_bound_of_lt_half_finiteSystem_input`,
`FloatingPointFormat.problem2_24_eval_eq_zero_y2_le_quarter_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_input_of_five_twelfths_lt`,
`FloatingPointFormat.problem2_24_eval_eq_zero_input_le_five_twelfths_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_eval_eq_zero_input_mem_five_eighteen_to_five_twelfths_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_y2_eq_two_mul_x_sub_half_of_finiteSystem_input_of_quarter_lt_of_lt_one_third`,
`FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_input_of_lt_three_tenths`,
`FloatingPointFormat.problem2_24_eval_eq_zero_input_ge_three_tenths_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_eval_eq_zero_input_mem_three_tenths_to_five_twelfths_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_y3_eq_neg_x_last_sub_distance_to_neg_const_product_le`,
`FloatingPointFormat.problem2_24_eval_eq_zero_last_sub_distance_to_neg_const_product_le_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_input_of_const_gt_one_third_of_lt_two_sub_const_div_five`,
`FloatingPointFormat.problem2_24_eval_eq_zero_input_ge_two_sub_const_div_five_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_input_of_three_eighths_lt`,
`FloatingPointFormat.problem2_24_eval_eq_zero_input_le_three_eighths_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_eval_ne_zero_of_finiteSystem_input_of_lt_fifty_three_one_sixty`,
`FloatingPointFormat.problem2_24_eval_eq_zero_input_ge_fifty_three_one_sixty_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_eval_eq_zero_input_mem_fifty_three_one_sixty_to_three_eighths_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_ieeeSingle_half_finiteSystem`,
`FloatingPointFormat.problem2_24_ieeeDouble_half_finiteSystem`,
`FloatingPointFormat.problem2_24_ieeeSingle_one_finiteSystem`,
`FloatingPointFormat.problem2_24_ieeeDouble_one_finiteSystem`,
`FloatingPointFormat.problem2_24_ieeeSingle_subnormalMantissa_one`,
`FloatingPointFormat.problem2_24_ieeeDouble_subnormalMantissa_one`,
`FloatingPointFormat.problem2_24_ieeeSingle_oneThird_rounds_to_upper`,
`FloatingPointFormat.problem2_24_ieeeSingle_one_third_not_finiteSystem`,
`FloatingPointFormat.problem2_24_ieeeDouble_one_third_not_finiteSystem`,
`FloatingPointFormat.problem2_24_ieeeSingle_finiteSystem_ne_one_third`,
`FloatingPointFormat.problem2_24_ieeeDouble_finiteSystem_ne_one_third`,
`FloatingPointFormat.problem2_24_ieeeSingle_exactExpr_ne_zero_of_finiteSystem`,
`FloatingPointFormat.problem2_24_ieeeDouble_exactExpr_ne_zero_of_finiteSystem`,
`FloatingPointFormat.problem2_24_ieeeSingle_eval_ne_zero_of_finiteSystem_intermediates`,
`FloatingPointFormat.problem2_24_ieeeDouble_eval_ne_zero_of_finiteSystem_intermediates`,
`FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_implies_exists_nonfinite_exact_intermediate`,
and
`FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_implies_exists_nonfinite_exact_intermediate`,
`FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_implies_later_nonfinite_exact_intermediate`,
`FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_implies_later_nonfinite_exact_intermediate`,
`FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_implies_second_or_third_nonfinite_exact_intermediate`,
`FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_implies_second_or_third_nonfinite_exact_intermediate`,
`FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_implies_last_two_nonfinite_exact_intermediate_of_lt_one_third`,
`FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_implies_last_two_nonfinite_exact_intermediate_of_lt_one_third`,
`FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_lt_one_third`,
`FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_lt_one_third`,
`FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_last_sum_abs_le_half_minSubnormalMagnitude`,
and
`FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_last_sum_abs_le_half_minSubnormalMagnitude`,
`FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_last_sum_eq_zero_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_last_sum_eq_zero_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_ieeeSingle_y3_eq_neg_x_of_eval_eq_zero_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_ieeeDouble_y3_eq_neg_x_of_eval_eq_zero_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_implies_y3_eq_neg_x_and_exists_nonfinite_exact_intermediate`,
and
`FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_implies_y3_eq_neg_x_and_exists_nonfinite_exact_intermediate`,
`FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_last_sub_distance_to_y2_le_half_of_finiteSystem_input`,
and
`FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_last_sub_distance_to_y2_le_half_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_last_sub_distance_to_zero_product_le_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_last_sub_distance_to_zero_product_le_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_last_sub_y2_bound_of_pos_finiteSystem_input`,
`FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_last_sub_y2_bound_of_pos_finiteSystem_input`,
`FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_input_mem_unit_interval_of_finiteSystem_input`,
and
`FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_input_mem_unit_interval_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_ieeeSingle_eval_ne_zero_of_finiteSystem_input_of_half_le`,
and
`FloatingPointFormat.problem2_24_ieeeDouble_eval_ne_zero_of_finiteSystem_input_of_half_le`,
`FloatingPointFormat.problem2_24_ieeeSingle_eval_zero_ne_zero`,
`FloatingPointFormat.problem2_24_ieeeDouble_eval_zero_ne_zero`,
`FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_input_pos_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_input_pos_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_input_mem_open_lower_half_of_finiteSystem_input`,
and
`FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_input_mem_open_lower_half_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_input_mem_tenth_to_half_of_finiteSystem_input`,
and
`FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_input_mem_tenth_to_half_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_input_mem_one_six_to_half_of_finiteSystem_input`,
and
`FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_input_mem_one_six_to_half_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_input_mem_nine_thirty_four_to_half_of_finiteSystem_input`,
and
`FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_input_mem_nine_thirty_four_to_half_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_input_mem_five_eighteen_to_half_of_finiteSystem_input`,
and
`FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_input_mem_five_eighteen_to_half_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_input_mem_five_eighteen_to_five_twelfths_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_input_mem_five_eighteen_to_five_twelfths_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_input_mem_three_tenths_to_five_twelfths_of_finiteSystem_input`,
and
`FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_input_mem_three_tenths_to_five_twelfths_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_ieeeSingle_three_eighths_finiteSystem`,
`FloatingPointFormat.problem2_24_ieeeDouble_three_eighths_finiteSystem`,
`FloatingPointFormat.problem2_24_ieeeSingle_eleven_thirty_two_finiteSystem`,
`FloatingPointFormat.problem2_24_ieeeDouble_eleven_thirty_two_finiteSystem`,
`FloatingPointFormat.problem2_24_ieeeSingle_one_third_upper_neighbor_finiteSystem`,
`FloatingPointFormat.problem2_24_ieeeDouble_one_third_upper_neighbor_finiteSystem`,
`FloatingPointFormat.problem2_24_ieeeSingle_one_quarter_finiteSystem`,
`FloatingPointFormat.problem2_24_ieeeDouble_one_quarter_finiteSystem`,
`FloatingPointFormat.problem2_24_ieeeSingle_second_exact_intermediate_finiteSystem_of_neg_one_mantissa_mem_upper_branch`,
`FloatingPointFormat.problem2_24_ieeeDouble_second_exact_intermediate_finiteSystem_of_neg_one_mantissa_mem_upper_branch`,
`FloatingPointFormat.problem2_24_ieeeSingle_finiteSystem_upper_branch_exists_neg_one_mantissa`,
`FloatingPointFormat.problem2_24_ieeeDouble_finiteSystem_upper_branch_exists_neg_one_mantissa`,
`FloatingPointFormat.problem2_24_ieeeSingle_second_exact_intermediate_finiteSystem_of_finiteSystem_upper_branch`,
`FloatingPointFormat.problem2_24_ieeeDouble_second_exact_intermediate_finiteSystem_of_finiteSystem_upper_branch`,
`FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_finiteSystem_upper_branch`,
`FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_finiteSystem_upper_branch`,
`FloatingPointFormat.problem2_24_ieeeSingle_upper_neighbor_le_of_finiteSystem_of_one_third_lt`,
`FloatingPointFormat.problem2_24_ieeeDouble_upper_neighbor_le_of_finiteSystem_of_one_third_lt`,
`FloatingPointFormat.problem2_24_ieeeSingle_upper_neighbor_le_of_finiteSystem_of_one_third_le`,
`FloatingPointFormat.problem2_24_ieeeDouble_upper_neighbor_le_of_finiteSystem_of_one_third_le`,
`FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_one_third_le`,
`FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_one_third_le`,
`FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_implies_third_exact_intermediate_nonfinite`,
`FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_implies_third_exact_intermediate_nonfinite`,
`FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_input_mem_fifty_three_one_sixty_to_three_eighths_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_input_mem_fifty_three_one_sixty_to_three_eighths_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_input_ge_two_sub_one_third_upper_neighbor_div_five_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_input_ge_two_sub_one_third_upper_neighbor_div_five_of_finiteSystem_input`,
`FloatingPointFormat.problem2_24_ieeeSingle_eval_eq_zero_input_mem_one_third_upper_neighbor_lower_to_three_eighths_of_finiteSystem_input`,
and
`FloatingPointFormat.problem2_24_ieeeDouble_eval_eq_zero_input_mem_one_third_upper_neighbor_lower_to_three_eighths_of_finiteSystem_input`.
These define the literal finite round-to-even path for
`(((x - 0.5) + x) - 0.5) + x`, expose its rounded intermediates, and close two
branches.  The exact real expression simplifies to `3*x - 1`, vanishes exactly
at `x = 1/3`, and is nonzero for every input different from `1/3`; the literal
constant `0.5` is proved to be finite in both IEEE single and IEEE double
formats.  If the last exact sum `y3 + x` is finite representable, the final
rounded addition is exact, so rounded zero is equivalent to exact zero of that
last sum and in particular forces `y3 = -x`.  If all four exact real
intermediates are finite representable, the evaluated path equals the literal
exact expression and simplifies to `3*x - 1`, so a zero result forces
`x = 1/3`, and any input known not to be `1/3` gives a nonzero result in this
branch.  Lean proves that `1/3` is not a finite
IEEE-single or IEEE-double value, using the single rounding fact
`fl(1/3) = 11184811 * 2^-25` and the existing double rounding fact; finite
single/double inputs are therefore not `1/3`, and the exact source expression is
nonzero for such inputs.  The zero-result branch-audit theorems first prove that
any finite IEEE single/double input producing zero in the modeled path must
leave the exact-intermediate branch.  The narrowed branch theorem then proves
that the first exact intermediate `x - 0.5` is finite on every finite zero
branch, so any remaining nonfinite exact real intermediate must be one of the
later three.  A sharper second/third theorem proves that if the second and
third exact real intermediates were both finite away from `1/3`, exact final
cancellation would force `x = 1/3`; hence any finite IEEE single/double zero
branch must fail at the second or third exact real intermediate.  The
upper-branch adapters classify finite IEEE single/double inputs in
`[upper-neighbor-above-1/3, 3/8]` as positive normalized exponent-`-1`
mantissas, prove the second exact intermediate finite there, and therefore
force a nonfinite third exact intermediate on any zero branch satisfying that
explicit upper-neighbor lower bound.  The adjacent no-gap lemmas prove that
finite inputs at or above `1/3` are in that explicit upper-neighbor interval,
so every finite IEEE single/double zero branch now forces a nonfinite third
exact real intermediate.  The remaining Problem 2.24 bridge is to turn that
nonfinite-third conclusion into a contradiction for the localized zero branch,
alongside the full IEEE special-value/flag lift.  The final-sum sharpening
further proves that such a zero result
would force `|y3+x|` to be at most half the smallest subnormal spacing in the
corresponding IEEE format.  The finite-grid separation lemmas prove every
finite-system value is an integer multiple of the smallest subnormal spacing,
so for finite inputs this tiny-sum branch collapses to exact final cancellation:
`y3+x = 0`, equivalently `y3 = -x`.  The third-step nearestness lemmas then
show that this cancellation makes `-x` a finite nearest-rounded value of
`y2 - 0.5`; in particular, comparing against the finite candidate `y2` forces
`|y2 + x - 0.5| <= 0.5` for any finite IEEE single/double zero counterexample.
Comparing against the finite candidate zero gives the product constraint
`x*(2*y2+x-1) <= 0`, hence at any positive finite zero counterexample
`2*y2+x <= 1`.
The first- and second-step nearestness lemmas compare the rounded intermediates
with the finite candidates `x`, `0`, and `y1`; together with the third-step
distance inequality they force `0 <= y2 + x <= 1` and then `0 <= x <= 1` for
any finite IEEE single/double zero counterexample.  The first-step comparison
against zero also splits `y1` around the midpoint: if `x >= 0.5` then
`0 <= y1 <= 2*x-1`, while if `x <= 0.5` then `2*x-1 <= y1 <= 0`.
The second-step comparison against zero gives the analogous cell for
`y2 = fl(y1+x)`: if `y1+x >= 0` then `0 <= y2 <= 2*(y1+x)`, while if
`y1+x <= 0` then `2*(y1+x) <= y2 <= 0`.
The second-step comparison against the finite candidate `x` gives
`(x-y2)*(2*y1+x-y2) <= 0`; combined with the third-step positive-input bound
and the first-step midpoint split, Lean proves there is no finite-system zero
counterexample with `x >= 0.5`, with IEEE single/double wrappers.  Lean also
proves the endpoint `x = 0` evaluates to `-1` when `0.5` and `1` are finite,
so any finite zero counterexample is strictly positive.  Comparing the third
subtraction against finite candidate `-0.5` forces `2*y2+x >= 0.5` in the
lower half, hence `y2 > 0` and `y1+x > 0`; combined with the candidate-`x`
product, this rules out `x < 1/6`.  The first-step comparison against the
finite candidate `-x` then gives `y1 <= 3*x-1` on that positive second-step
branch; combined with the second-step sign cell and the third-step lower
bound, this further rules out `x < 9/34`.  Sterbenz exactness then gives
`y1 = x - 0.5` throughout the narrowed lower branch, which also proves the
first exact intermediate is finite on every modeled finite zero branch; the
sub-third exact-second-addition theorem proves the second exact intermediate is
finite whenever a finite zero branch has `x < 1/3`.  If the third exact
intermediate were finite there, the third subtraction would be exact, forcing
`y3 = 2*x-1`; exact final cancellation would then give `x = 1/3`, a
contradiction.  Thus in the sub-third branch the nonfinite witness must be the
third exact real intermediate itself.  The adjacent no-gap and upper-neighbor
classification lemmas close the branch at or above `1/3` to the same third
exact-intermediate nonfinite witness.  The same second- and third-step
inequalities rule out `x < 5/18`.  The third-step comparison against
finite candidate `y1` gives `2*y2-y1+x <= 1` on the positive lower branch;
with `y1 = x-0.5` this proves `y2 <= 0.25`, and the candidate-`x` second-step
product rules out `x > 5/12`.  In the sub-third branch, the second addition is
Sterbenz-exact, `y2 = 2*x-0.5`; combined with the third-step lower bound, this
rules out `x < 3/10`.  For generic finite formats without extra dyadic
candidate hypotheses, the remaining modeled branch is `3/10 <= x <= 5/12`.
Specializing `-3/8` keeps the IEEE upper endpoint at `x <= 3/8`, while the
parametric negative-candidate theorem applied to the upper adjacent
representable values `11184811 * 2^-25` (single) and
`6004799503160662 * 2^-54` (double) sharpens the current IEEE lower endpoints
to `(2 - 11184811 * 2^-25)/5` and `(2 - 6004799503160662 * 2^-54)/5`.
The finite-grid, interval-to-mantissa, adjacent no-gap, and third-intermediate
representability adapters now close the modeled finite IEEE path:
`problem2_24_ieeeSingle_eval_ne_zero_of_finiteSystem_input` and
`problem2_24_ieeeDouble_eval_ne_zero_of_finiteSystem_input` prove that no
finite single/double input evaluates to zero in the finite round-to-even model.
Remaining Problem 2.24 scope is the lift from this finite model to full IEEE
operation semantics with flags, traps, infinities, and NaNs.

Chapter 2 Kahan FMA determinant accuracy (Problem 2.25):
`problem2_25_finiteRoundedProduct`,
`problem2_25_finiteFmaDetWithRoundedProduct`,
`problem2_25_roundedProductResidualsRepresentable`,
`problem2_25_finiteRoundedProduct_finiteSystem`,
`problem2_25_fmaCore_eq_det2x2`,
`problem2_25_finiteFmaCore_eq_det2x2_of_exact_residuals`,
`problem2_25_finiteFmaDet_signedRelErrorWitness_lt`,
`problem2_25_finiteFmaDet_relError_lt_unitRoundoff`,
`problem2_25_finiteFmaDetWithRoundedProduct_signedRelErrorWitness_lt`, and
`problem2_25_finiteFmaDetWithRoundedProduct_relError_lt_unitRoundoff`, with
`problem2_25_finiteFmaDetWithRoundedProduct_highRelativeAccuracy`.  These
formalize the source determinant `det([[a,b],[c,d]]) = a*d - b*c`: if the FMA
residuals `a*d-w` and `w-b*c` are exactly representable, then their finite FMA
core sums to the exact determinant for any rounded product `w`; a final
finite-normal rounding step then satisfies the strict unit-roundoff
relative-error model.  The source-shaped wrapper now wires in the first
computed quantity `w = fl(b*c)`, proves that this rounded product is finite in
the model, names the exact-residual side condition after that rounded product,
and packages the same signed-witness and relative-error theorem for the
displayed algorithm.  Remaining scope is the full binary/IEEE proof that the residual
representability hypotheses hold for the intended inputs, plus special values,
flags, traps, signed zeros, infinities, and NaNs.

Chapter 2 reciprocal Newton derivation (Problem 2.26):
`reciprocalNewtonCorrection`, `reciprocalNewtonStep`,
`reciprocalNewtonStepIter`,
`reciprocalNewtonRoundedStep`, `reciprocalNewtonRoundedStepErrorEval`,
`reciprocalNewtonRoundedResidual`,
`reciprocalNewtonRoundedStepIter`,
`reciprocalNewtonRoundedResidualErrorEval`,
`reciprocalNewtonRoundedResidualAbsBound`,
`reciprocalNewtonCorrection_eq_step`, `reciprocalNewtonStep_residual_sq`,
`reciprocalNewtonStep_error_sq`, `reciprocalNewtonStep_fixed_point`,
`reciprocalNewtonStepIter_residual_pow_two`,
`division_eq_multiply_by_reciprocal`,
`divisionViaReciprocal_error_eq_residual`,
`reciprocalNewtonStep_division_error_sq`,
`reciprocalNewtonStepIter_division_error_pow_two`,
`reciprocalNewtonRoundedResidualErrorEval_zero_errors`,
`reciprocalNewtonRoundedStepErrorEval_residual_eq`,
`reciprocalNewtonRoundedResidualErrorEval_eq_sq_plus_roundoff`,
`reciprocalNewtonRoundedResidualErrorEval_abs_le`,
`reciprocalNewtonRoundedResidualAbsBound_le_radius`,
`reciprocalNewtonRoundedResidualAbsBound_le_small_radius`,
`reciprocalNewtonRoundedResidualErrorEval_abs_le_small_radius`,
`reciprocalNewtonRoundedResidualErrorEval_abs_le_self_radius`,
`reciprocalNewtonRoundedResidualErrorEvalIter`,
`reciprocalNewtonRoundedResidualEnvelope`,
`reciprocalNewtonRoundedResidualEnvelope_nonneg`,
`reciprocalNewtonRoundedResidualEnvelope_le_self_radius`,
`reciprocalNewtonRoundedResidualEnvelope_le_roundoff_floor`,
`reciprocalNewtonRoundedResidualEnvelope_le_geometric_floor`,
`reciprocalNewtonRoundedResidualErrorEvalIter_abs_le_envelope`,
`reciprocalNewtonRoundedResidualErrorEvalIter_abs_le_envelope_of_self_radius`,
`reciprocalNewtonRoundedResidualErrorEvalIter_abs_le_self_radius`,
`reciprocalNewtonRoundedResidualErrorEvalIter_abs_le_roundoff_floor`,
`reciprocalNewtonRoundedResidualErrorEvalIter_abs_le_geometric_floor`,
`reciprocalNewtonRoundedStep_eq_errorEval`,
`reciprocalNewtonRoundedResidual_eq_errorEval`,
`reciprocalNewtonRoundedResidual_eq_residualErrorEval`,
`reciprocalNewtonRoundedResidual_abs_le_small_radius`,
`reciprocalNewtonRoundedResidual_abs_le_self_radius`,
`reciprocalNewtonRoundedStepIter_residual_abs_le_envelope_of_self_radius`,
`reciprocalNewtonRoundedStepIter_residual_abs_le_geometric_floor`,
`reciprocalNewtonRoundedStepIter_residual_abs_le_roundoff_floor`,
`reciprocalNewtonRoundedStepIter_division_error_abs_le_geometric_floor`,
`reciprocalNewtonRoundedStepIter_division_error_abs_le_roundoff_floor`,
`FloatingPointFormat.reciprocalNewtonFiniteStep`,
`FloatingPointFormat.reciprocalNewtonFiniteStepIter`,
`FloatingPointFormat.reciprocalNewtonFiniteStep_eq_step_of_finiteSystem`,
`FloatingPointFormat.reciprocalNewtonFiniteStep_residual_sq_of_finiteSystem`,
`FloatingPointFormat.reciprocalNewtonFiniteStep_error_sq_of_finiteSystem`,
`FloatingPointFormat.reciprocalNewtonFiniteStepIter_residual_sq_of_finiteSystem`,
`FloatingPointFormat.reciprocalNewtonFiniteStepIter_residual_pow_two_of_finiteSystem`,
`FloatingPointFormat.reciprocalNewtonFiniteStepIter_error_pow_two_of_finiteSystem`,
and
`FloatingPointFormat.reciprocalNewtonFiniteStepIter_division_error_pow_two_of_finiteSystem`.
These prove the exact real-arithmetic derivation for Newton's method applied to
`f(x) = a - 1/x = 0`, expose the three local standard-model errors in one
rounded step, rewrite the rounded residual as a recurrence in the incoming
exact residual `1-a*x`, prove that zero local errors reduce that recurrence
to the exact residual square, and lift the exact residual law to stored exact
iterates as `1 - a*x_n = (1-a*x_0)^(2^n)`.  Lean now also formalizes the
source sentence `num/denom = num*(1/denom)` and propagates the reciprocal
residual law into exact division-error theorems for one Newton step and stored
exact iterates.  The rounded recurrence is also
decomposed as the
ideal Newton square plus explicit local-error perturbations and bounded by the
conservative one-step radius
`reciprocalNewtonRoundedResidualAbsBound`; the small-radius corollaries give
the readable one-step estimate `rho^2 + 22*u` when `|1-a*x| <= rho <= 1` and
`u <= 1`, and a small-ball preservation corollary keeps the residual below
`rho` when `rho <= 1/2` and `44*u <= rho`; the iterated residual-recurrence
theorem proves this invariant for every finite sequence of local errors.  The
envelope theorem proves every finite residual iterate is bounded by the scalar
recurrence `E_{n+1} = E_n^2 + 22*u` whenever that envelope stays in `[0,1]`.
Lean now also proves that the envelope side conditions follow from
`rho <= 1/2` and `44*u <= rho`, and in particular that starting inside
`44*u` keeps both the envelope and every finite rounded-residual iterate below
the explicit roundoff floor `44*u` when `u <= 1/88`.  The closed-form
rate corollary bounds the scalar envelope, and hence every finite
standard-model residual iterate, by `rho / 2^n + 44*u`.  The concrete
stored rounded trace `reciprocalNewtonRoundedStepIter` now inherits the same
envelope, geometric-plus-floor, and `44*u` floor bounds for its actual stored
residuals; multiplying that stored reciprocal estimate by a numerator gives
the corresponding absolute division-error bounds scaled by `|num/denom|`.
The concrete finite round-to-even trace inherits the exact squared
residual/error identities whenever `a*x`, `2-a*x`, and `x*(2-a*x)` are finite
representable.  The finite stored-iteration theorems lift this exactness to
every stored finite iterate under per-step exact-intermediate finiteness
hypotheses, including the doubled-exponent residual, reciprocal-error, and
division-error laws.
Full IEEE exceptional values remain separate.

Chapter 2 residual convergence test (Problem 2.27):
`problem2_27_residual`, `problem2_27_fullAccuracy`,
`problem2_27_residual_eq_zero_iff_fullAccuracy`,
`problem2_27_fullAccuracy_iff_eq_div`,
`problem2_27_zero_exact_residual_of_additive_model_normal_branch`,
`problem2_27_zero_exact_residual_or_underflow_bound_of_additive_model`,
`problem2_27_zero_exact_residual_or_strict_underflow_bound_of_strict_model`,
`problem2_27_fullAccuracy_of_zero_residual_normal_branch`,
`problem2_27_fullAccuracy_or_underflow_bound_of_zero_residual_model`,
`FloatingPointFormat.problem2_27_computedResidual`,
`FloatingPointFormat.problem2_27_convergenceTest`,
`FloatingPointFormat.problem2_27_convergenceTest_iff_fullAccuracy_of_exact_residual_path`,
`FloatingPointFormat.problem2_27_convergenceTest_fullAccuracy_or_underflow_bound_of_additive_model`,
`FloatingPointFormat.problem2_27_convergenceTest_fullAccuracy_or_strict_underflow_bound_of_strict_model`,
`FloatingPointFormat.problem2_27_convergenceTest_fullAccuracy_of_additive_model_normal_branch`,
`FloatingPointFormat.problem2_27_convergenceTest_of_fullAccuracy_additive_model_normal_branch`,
`FloatingPointFormat.problem2_27_convergenceTest_iff_fullAccuracy_of_additive_model_normal_branch`,
`FloatingPointFormat.problem2_27_convergenceTest_eq_div_of_additive_model_normal_branch`,
`FloatingPointFormat.problem2_27_convergenceTest_iff_eq_div_of_additive_model_normal_branch`,
`FloatingPointFormat.problem2_27_convergenceTest_eq_div_or_underflow_bound_of_additive_model`,
and
`FloatingPointFormat.problem2_27_convergenceTest_eq_div_or_strict_underflow_bound_of_strict_model`.
These formalize the source residual test for `z = x/y`: an exact residual
zero is equivalent to `y*z = x` and, for `y != 0`, to `z = x/y`; a zero
computed residual under (2.8) certifies full accuracy in the no-underflow
branch `eta = 0`, and in that branch the test is now equivalent to full
accuracy, hence equivalent to `z = x/y` for `y != 0`.  The general
gradual-underflow branch
certifies either the exact quotient or that the exact residual is within the
additive eta-bound, with a strict eta-bound under the strict no-half-tie model.
Full IEEE
operation semantics, flags, traps, special values, and a concrete rounded
iteration remain separate.

Chapter 2 tie-rule decimal example (§2.9):
`FloatingPointFormat.nearestAdjacentRoundToOdd`,
`FloatingPointFormat.nearestAdjacentRoundToOdd_eq_right_of_tie_even`,
`FloatingPointFormat.nearestAdjacentRoundToOdd_eq_left_of_tie_odd`,
`FloatingPointFormat.decimal_2445_roundToEven_chain`, and
`FloatingPointFormat.decimal_2445_roundToOdd_chain`.  This formalizes the
source's exact `2.445` example: round-to-even gives `2.445 -> 2.44 -> 2.4`,
while round-to-odd gives `2.445 -> 2.45 -> 2.5`.  The local add/sub traces
`FloatingPointFormat.decimalOnePlaceRoundToEven_reiserKnuth_stable_from_one`
and
`FloatingPointFormat.decimalOnePlaceRoundToOdd_reiserKnuth_stable_after_first_step`
give concrete one-decimal Reiser--Knuth-shaped stability instances, while
`FloatingPointFormat.decimalOnePlaceRoundAway_drift_first_two_steps` gives the
contrasting round-away drift trace from `1.1` to `1.2`.  The full general
Reiser--Knuth stability theorem remains open.

Chapter 2 finite nonassociativity examples (§2.9):
`FloatingPointFormat.decimalOneDigitTwoExponentFormat`,
`FloatingPointFormat.decimalOneDigitTwoExponent_add_ten_four_rounds_to_ten`,
`FloatingPointFormat.decimalOneDigitTwoExponent_add_ten_neg_four_exact`,
`FloatingPointFormat.decimalOneDigitTwoExponent_add_four_neg_four_exact`,
`FloatingPointFormat.decimalOneDigitTwoExponent_add_ten_zero_exact`, and
`FloatingPointFormat.decimalOneDigitTwoExponent_roundToEven_add_nonassociative`.
These give a no-overflow finite round-to-even addition counterexample in a
one-digit decimal format with exponents `1` and `2`:
`(10 ⊕ 4) ⊕ (-4) = 6` but `10 ⊕ (4 ⊕ (-4)) = 10`.  The matching subtraction
example is closed by
`FloatingPointFormat.decimalOneDigitTwoExponent_sub_ten_neg_four_rounds_to_ten`,
`FloatingPointFormat.decimalOneDigitTwoExponent_sub_ten_four_exact`,
`FloatingPointFormat.decimalOneDigitTwoExponent_sub_neg_four_four_exact`,
`FloatingPointFormat.decimalOneDigitTwoExponent_sub_ten_neg_eight_rounds_to_twenty`,
and
`FloatingPointFormat.decimalOneDigitTwoExponent_roundToEven_sub_nonassociative`:
`(10 ⊖ (-4)) ⊖ 4 = 6` but `10 ⊖ ((-4) ⊖ 4) = 20`.  A one-digit decimal
format with exponents `0`, `1`, and `2` gives a multiplication counterexample:
`FloatingPointFormat.decimalOneDigitThreeExponent_roundToEven_mul_nonassociative`
proves `((0.2 ⊗ 0.6) ⊗ 3) = 0.3` but
`0.2 ⊗ (0.6 ⊗ 3) = 0.4`.  The same `0..2` format also gives
`FloatingPointFormat.decimalOneDigitThreeExponent_roundToEven_div_nonassociative`:
`(0.1 ⊘ 0.1) ⊘ 0.1 = 10` but
`0.1 ⊘ (0.1 ⊘ 0.1) = 0.1`; this division example is inherited from exact
representable divisions rather than an inexact rounding step.  A single general
schema covering all primitive operations remains open.

Chapter 2 local monotonicity foundation (§2.9):
`FloatingPointFormat.nearestAdjacentRoundToEven_eq_left_or_right`,
`FloatingPointFormat.left_le_nearestAdjacentRoundToEven`,
`FloatingPointFormat.nearestAdjacentRoundToEven_le_right`, and
`FloatingPointFormat.nearestAdjacentRoundToEven_monotone_on_ordered_bracket`;
the analogous round-away and round-to-odd endpoints and same-bracket
monotonicity are exposed by
`FloatingPointFormat.nearestAdjacentRoundAway_monotone_on_ordered_bracket` and
`FloatingPointFormat.nearestAdjacentRoundToOdd_monotone_on_ordered_bracket`.
The directed endpoint selectors are covered by
`FloatingPointFormat.adjacentRoundTowardNegative_monotone_on_ordered_bracket`,
`FloatingPointFormat.adjacentRoundTowardPositive_monotone_on_ordered_bracket`,
`FloatingPointFormat.adjacentRoundTowardZero_monotone_on_nonnegative_ordered_bracket`,
and
`FloatingPointFormat.adjacentRoundTowardZero_monotone_on_nonpositive_ordered_bracket`.
These prove that, on a fixed ordered adjacent bracket, the modeled local
nearest and directed selectors cannot move left when the exact input moves
right; toward-zero is intentionally split into nonnegative and nonpositive
brackets because a bracket crossing zero is not monotone for that local
selector.  The overflow branch of the total finite selectors is now lifted by
`FloatingPointFormat.not_finiteUnderflowRange_of_finiteOverflowRange`,
`FloatingPointFormat.finiteOverflowSaturation_monotone`,
`FloatingPointFormat.finiteRoundAway_monotone_on_overflow_branch`,
`FloatingPointFormat.finiteRoundToEven_monotone_on_overflow_branch`,
the directed overflow-branch monotonicity theorems, and
`FloatingPointFormat.finiteRoundToMode_monotone_on_overflow_branch`.  The
finite-underflow toward-zero branch is also closed on sign-uniform inputs by
`FloatingPointFormat.finiteUnderflowRoundTowardZeroNonneg_eq_floor_mul`,
`FloatingPointFormat.finiteUnderflowRoundTowardZeroNonneg_monotone`,
`FloatingPointFormat.finiteRoundTowardZero_monotone_on_nonnegative_underflow_branch`,
and
`FloatingPointFormat.finiteRoundTowardZero_monotone_on_nonpositive_underflow_branch`.
The directed finite-underflow branches for rounding toward positive and
negative infinity are closed by
`FloatingPointFormat.finiteUnderflowRoundTowardPositiveNonneg_eq_ceil_mul_of_nonneg_underflow`,
`FloatingPointFormat.finiteUnderflowRoundTowardPositiveNonneg_monotone_on_underflow`,
`FloatingPointFormat.finiteUnderflowRoundTowardPositive_monotone_on_underflow`,
`FloatingPointFormat.finiteUnderflowRoundTowardNegative_monotone_on_underflow`,
`FloatingPointFormat.finiteRoundTowardPositive_monotone_on_underflow_branch`,
and
`FloatingPointFormat.finiteRoundTowardNegative_monotone_on_underflow_branch`.
Full finite-format operation monotonicity still needs the nearest-underflow,
normal, and cross-branch selector lifts plus primitive-operation monotonicity
assumptions; full IEEE monotonicity remains open.

Chapter 2 chopping/toward-zero bias (§2.9):
`FloatingPointFormat.finiteRoundTowardZero_le_of_nonneg`,
`FloatingPointFormat.le_finiteRoundTowardZero_of_nonpos`,
`FloatingPointFormat.finiteRoundTowardZero_error_nonpos_of_nonneg`,
`FloatingPointFormat.finiteRoundTowardZero_error_nonneg_of_nonpos`,
`FloatingPointFormat.finiteRoundToModeOp_towardZero_error_nonpos_of_exact_nonneg`,
`FloatingPointFormat.finiteRoundTowardZero_sum_errors_nonpos_of_nonneg`,
`decimalChopThree`, `decimalChopThree_abs_error_lt_one_thousandth`,
`decimalChopThree_grid_eq`, and `decimalChopThree_sum_errors_nonpos`.
This formalizes the finite-format core of Higham's chopping note: rounding
toward zero gives nonpositive final error for nonnegative exact results and
nonnegative final error for nonpositive exact results, and accumulated
nonnegative exact-result chopping errors have a nonpositive total bias.  The
concrete Vancouver three-decimal final-value policy is modeled by floor-scaling
to `10^3`: exact three-decimal grid values are fixed, each final error is below
`0.001`, and finite accumulated final errors are nonpositive.  The historical
Vancouver Stock Exchange update data and full decimal/IEEE execution trace
are closed as an empirical-source-output carve-out; if pursued, they should be
an experiment/data replay rather than a Lean theorem obligation.

Chapter 2 additive underflow model (2.8): `additiveErrorWitness`, `additiveUnderflowModelWitness`, `strictAdditiveUnderflowModelWitness`, `additiveUnderflowModelWitness_normal_branch`, `strictAdditiveUnderflowModelWitness_normal_branch`, `FloatingPointFormat.gradualUnderflowEtaBound`, `FloatingPointFormat.flushToZeroEtaBound`, `FloatingPointFormat.gradualUnderflowEtaBound_le_flushToZeroEtaBound`, `FloatingPointFormat.gradualUnderflowEtaBound_eq_half_minSubnormalMagnitude`, `FloatingPointFormat.finiteUnderflowNoHalfTie`, `FloatingPointFormat.nearestRoundingToFinite_absError_le_gradualUnderflowEtaBound_of_finiteUnderflowRange`, `FloatingPointFormat.nearestRoundingToFinite_absError_lt_gradualUnderflowEtaBound_of_finiteUnderflowRange_of_noHalfTie`, `FloatingPointFormat.finiteRoundToEven_absError_le_gradualUnderflowEtaBound_of_finiteUnderflowRange`, `FloatingPointFormat.finiteRoundToEven_strictAdditiveUnderflowModel_underflow_branch_of_finiteUnderflowRange_of_noHalfTie`, `FloatingPointFormat.finiteRoundToEvenOp_additiveUnderflowModel_underflow_branch_of_finiteUnderflowRange`, `FloatingPointFormat.finiteRoundToEvenSqrt_additiveUnderflowModel_underflow_branch_of_finiteUnderflowRange`, `FloatingPointFormat.finiteRoundToMode_additiveUnderflowModel_underflow_branch_of_finiteUnderflowRange_flush`, `FloatingPointFormat.finiteRoundToModeOp_additiveUnderflowModel_underflow_branch_of_finiteUnderflowRange_flush`, `FloatingPointFormat.finiteRoundToModeSqrt_additiveUnderflowModel_underflow_branch_of_finiteUnderflowRange_flush`, `FloatingPointFormat.ieeeRoundToModeOpResult_ieeeUnderflowModeResult_and_flushAdditiveUnderflowModel`, and `FloatingPointFormat.ieeeRoundToModeSqrtResult_ieeeUnderflowModeResult_and_flushAdditiveUnderflowModel`.  This formalizes (2.8)'s algebra and constants, proves `u * alpha` is half a subnormal spacing, connects the finite-normal no-underflow branch with `eta = 0`, proves the non-strict gradual-underflow additive branch for nearest/even source-facing finite wrappers, adds all-mode flush-bound finite underflow adapters for mode/op/sqrt wrappers, and proves strict `<` variants under the visible no-half-cell-tie side condition.  Full IEEE traps, broader special values, and concrete IEEE operation semantics remain open.

Chapter 2 finite-normal-range nearest-rounding theorem (non-strict and strict source-relative): `FloatingPointFormat.unboundedNormalizedSystem_normalizedSystem_of_finiteNormalRange`, `FloatingPointFormat.nearestRoundingToUnbounded_output_finite_of_minNormalMagnitude_le_of_le_maxFiniteMagnitude`, `FloatingPointFormat.nearestRoundingToUnbounded_output_finite_of_neg_maxFiniteMagnitude_le_of_le_neg_minNormalMagnitude`, `FloatingPointFormat.exists_nearestRoundingToFinite_signedRelErrorWitness_positive_finiteNormalRange`, `FloatingPointFormat.exists_nearestRoundingToFinite_signedRelErrorWitness_negative_finiteNormalRange`, `FloatingPointFormat.exists_nearestRoundingToFinite_signedRelErrorWitness_finiteNormalRange`, `FloatingPointFormat.nearestRoundingToFinite_signedRelErrorWitness_of_finiteNormalRange`, `FloatingPointFormat.finiteNormalFl`, `FloatingPointFormat.finiteNormalFl_signedRelErrorWitness`, `FloatingPointFormat.exists_nearestRoundingToFinite_signedRelErrorWitness_lt_positive_finiteNormalRange`, `FloatingPointFormat.exists_nearestRoundingToFinite_signedRelErrorWitness_lt_negative_finiteNormalRange`, `FloatingPointFormat.exists_nearestRoundingToFinite_signedRelErrorWitness_lt_finiteNormalRange`, `FloatingPointFormat.nearestRoundingToFinite_signedRelErrorWitness_lt_of_finiteNormalRange`, `FloatingPointFormat.finiteNormalRange_ne_zero`, `FloatingPointFormat.sourceRoundAwayEvidence`, `FloatingPointFormat.sourceRoundAwayEvidence_relErrorComputedDenom_le_unitRoundoff`, `FloatingPointFormat.sourceRoundToEvenEvidence`, `FloatingPointFormat.sourceRoundToEvenEvidence_relErrorComputedDenom_le_unitRoundoff`, `FloatingPointFormat.exists_finiteNormalRoundAway_signedRelErrorWitness_lt_finiteNormalRange`, `FloatingPointFormat.exists_finiteNormalRoundToEven_signedRelErrorWitness_lt_finiteNormalRange`, `FloatingPointFormat.finiteNormalRoundAway`, `FloatingPointFormat.finiteNormalRoundAway_spec`, `FloatingPointFormat.finiteNormalRoundAway_nearestRoundingToFinite`, `FloatingPointFormat.finiteNormalRoundAway_sourceRoundAwayEvidence`, `FloatingPointFormat.finiteNormalRoundAway_signedRelErrorWitness_lt`, `FloatingPointFormat.finiteNormalRoundAway_inverseRelErrorModel`, `FloatingPointFormat.finiteNormalRoundAway_inverseRelErrorWitness`, `FloatingPointFormat.finiteNormalRoundToEven`, `FloatingPointFormat.finiteNormalRoundToEven_spec`, `FloatingPointFormat.finiteNormalRoundToEven_nearestRoundingToFinite`, `FloatingPointFormat.finiteNormalRoundToEven_sourceRoundToEvenEvidence`, `FloatingPointFormat.finiteNormalRoundToEven_signedRelErrorWitness_lt`, `FloatingPointFormat.finiteNormalRoundToEven_inverseRelErrorModel`, `FloatingPointFormat.finiteNormalRoundToEven_inverseRelErrorWitness`, and `FloatingPointFormat.finiteNormalFl_signedRelErrorWitness_lt`.

Chapter 2 finite-normal-range inverse nearest-rounding theorem: `FloatingPointFormat.nearestRoundingToUnbounded_abs_sub_le_unitRoundoff_mul_rounded_of_realOrderAdjacent_between`, `FloatingPointFormat.nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_of_realOrderAdjacent_between`, `FloatingPointFormat.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_nonzero`, `FloatingPointFormat.exists_nearestRoundingToFinite_relErrorComputedDenom_le_unitRoundoff_finiteNormalRange`, `FloatingPointFormat.exists_nearestRoundingToFinite_inverseRelErrorModel_finiteNormalRange`, `FloatingPointFormat.exists_nearestRoundingToFinite_inverseRelErrorWitness_finiteNormalRange`, `FloatingPointFormat.finiteNormalFl`, `FloatingPointFormat.finiteNormalFl_inverseRelErrorWitness`, `FloatingPointFormat.finiteNormalRoundAway`, `FloatingPointFormat.finiteNormalRoundAway_inverseRelErrorWitness`, `FloatingPointFormat.finiteNormalRoundToEven`, and `FloatingPointFormat.finiteNormalRoundToEven_inverseRelErrorWitness`.

Chapter 2 IEEE single/double parameter tuples, ulp/wobbling adapters, and epsilon conventions: `FloatingPointFormat.ieeeSingleFormat`, `FloatingPointFormat.ieeeSingleFormat_params`, `FloatingPointFormat.ieeeSingleFormat_machineEpsilon`, `FloatingPointFormat.ieeeSingleFormat_unitRoundoff`, `FloatingPointFormat.ieeeSingleFormat_ulpAtExponent`, `FloatingPointFormat.ieeeDoubleFormat`, `FloatingPointFormat.ieeeDoubleFormat_params`, `FloatingPointFormat.ieeeDoubleFormat_machineEpsilon`, `FloatingPointFormat.ieeeDoubleFormat_unitRoundoff`, `FloatingPointFormat.ieeeDoubleFormat_ulpAtExponent`, `FloatingPointFormat.matlabIeeeDoubleEps`, `FloatingPointFormat.fortranEpsilon`, `FloatingPointFormat.ieeeSingleFormat_fortranEpsilon`, `FloatingPointFormat.ieeeDoubleFormat_fortranEpsilon`, `FloatingPointFormat.ulpAtExponent`, `FloatingPointFormat.normalizedValue_wobblingPrecision_bounds`, `FloatingPointFormat.realOrderAdjacentNormalized_relativeSpacing_bounds_left`, and `FloatingPointFormat.ieeeSingleFormat_realOrderAdjacentNormalized_relativeSpacing_bounds_left`.

### Algorithms

| Algorithm | Source | Key results |
|---|---|---|
| Dot product | Higham §3.1, §3.3--§3.4 | `dotProduct_factor_expansion_succ` — local-factor expansion for (3.1)--(3.2); `dotProduct_error_bound_101_succ` — small-`nu` 1.01*n*u forward bound; `dotProduct_error_bound` — tight γ(n) bound; `blockDotProduct_error_bound`, `twoPieceDotProduct_error_bound`, and `blockDotProduct_real_index_ge_optimum` — equal-block `gamma_{n/k+k-1}` route and `k ~= sqrt(n)` balancing rule; `extendedDotProduct_error_bound` and `extendedExactMulDotProduct_error_bound` — extended-precision inner products with final rounding; `sumTreeDotProduct_error_bound`, `balancedTreeDotProduct_error_bound`, and `clog2PairwiseDotProduct_error_bound` — product-first tree/pairwise dot-product bounds; `runningError_bound_from_local_errors` — Algorithm 3.2 recurrence core; `fl_runningDotProduct_error_bound_from_inverse_models` — concrete running-error loop under source inverse-model witnesses |
| Complex dot and matrix-vector backward error | Higham Problem 3.7 | `complexDotProduct_backward_stable_y`, `complexDotProduct_backward_stable_x`, `complexMatVec_backward_error` — complex-modulus analogues of the real dot-product and matrix-vector backward-error results |
| Continued fractions | Higham Problem 3.3 | `continuedFraction_step_error_le`, `continuedFraction_running_error_bound` — backward-recurrence running-error propagation with the local residual and denominator-separation hypotheses exposed explicitly |
| Matrix-vector product | Higham §3.5 | `fl_matVecSaxpy_eq_sdot`, `matVec_backward_error`, `matVec_error_bound`, `matVec_error_bound_infNorm`, `matVec_error_bound_oneNorm`, `matVec_error_bound_infNormRect`, `matVec_error_bound_oneNormRect` |
| Outer product | Higham §3.1 | `outerProduct_error_bound`, `outerProduct_error_decomposition`, `fl_outerProduct_counterexample_not_global_backward` |
| Matrix multiplication | Higham §3.5, Problems 3.5--3.6 | `matMul_error_bound`, `matMul_error_bound_frobNorm_majorant`, `matMul_error_bound_rectOpNorm2Le_majorant`, `matMul_error_bound_oneNorm`, `matMul_error_bound_oneNormRect`, `matMul_error_bound_infNormRect`, `matMul_error_bound_frobNormRect`, `matMul_error_bound_frobNorm`, `matMul_error_bound_opNorm2Le_frob`, `matMul_backward_error_common_A_of_inverse`, `matMul_backward_error_common_B_of_inverse`, `matMulRelativeBackwardFeasible_residual_entry_le`, `matMulRelativeBackwardFeasible_sqrt_lower_bound_entry`, `matMulWeightedBackwardFeasible_residual_entry_le`, `matMulWeightedBackwardFeasible_sqrt_lower_bound_entry`, `matMulMixedBackwardForwardFeasible`, `fl_matMul_counterexample_not_global_backward_A_gamma`, `matMul_forward_bound_sharp_A`, `matMul_forward_bound_sharp_B` |
| Matrix-product perturbation | Higham §3.7, Lemmas 3.6--3.8, Problems 3.9--3.10 | `matSeqProd_normwise_perturbation_bound` — normwise product perturbation under an abstract consistent-norm interface; `matSeqProd_mixed_normwise_perturbation_bound` — mixed-norm induction core for the Frobenius/operator-2 Lemma 3.7 variant; `matSeqProd_componentwise_perturbation_bound` — componentwise perturbation bound for finite matrix products; `matPrefixProd_error_bound_from_local_errors`, `matPrefixProd_error_bound_uniform` — finite-budget sequential matrix-product error accumulation behind the `k n^2 u + O(u^2)` problem bound |
| Difference of squares | Higham Problem 3.8 | `fl_squareDiff_direct_error_bound`, `fl_squareDiff_factored_rel_error`, `fl_squareDiff_factored_error_bound` — compares the cancellation-sensitive direct route with the factored route whose bound is proportional to `|x^2-y^2|` |
| Kahan absolute-value traces | Higham Problem 3.11 | `kahanAbsoluteExactFromSquareSteps_eq_abs`, `kahanAbsoluteExact_fifty_eq_abs`, `kahanAbsoluteExact_seventyFive_eq_abs`, `kahanAbsoluteFiniteRoundToEvenTrace`, `kahanAbsoluteProblem311FiniteTraceVector`, `kahanAbsoluteProblem311IeeeDouble_initialSquare_exact`, `kahanAbsoluteProblem311Inputs_ieeeDouble_finiteSystem`, `kahanAbsoluteProblem311IeeeDouble_initialSquare_firstSqrt_exact`, `kahanAbsoluteProblem311FiniteTraceVector_ieeeDouble_m75_eq_reduced`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_thirtyFour_succ`, `kahanAbsoluteIeeeDouble_square_eq_zero_of_abs_mul_lt_half_minSubnormal`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_eq_zero_of_abs_mul_lt_half_minSubnormal`, `kahanAbsoluteProblem311_sunM75_outputs_of_phase_laws`, `kahanAbsoluteProblem311_i486M75_outputs_of_allOne_phase_laws`, `kahanAbsoluteProblem311_i486M50_display4_self` - closes the formalizable mechanisms and ledger classification for Problem 3.11. The historical 486DX/Sun printed rows are recorded as `empirical-source-output` because the source omits the exact MATLAB/platform/formatting semantics; exact reproduction belongs to an experiment or explicit machine model, not the full Chapter 3 Lean gate. |
| Kahan absolute-value square-30 frontier | Higham Problem 3.11 | `kahanAbsoluteIeeeDoubleOneBillionSeventyThreeMillionSevenHundredFortyOneThousandSevenHundredSixtyEightUlpsBelowOne`, `kahanAbsoluteIeeeDouble_square_fiveHundredThirtySixMillionEightHundredSeventyThousandNineHundredUlpsBelowOne_eq_oneBillionSeventyThreeMillionSevenHundredFortyOneThousandSevenHundredSixtyEightUlpsBelowOne`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_fiveHundredThirtySixMillionEightHundredSeventyThousandNineHundredUlpsBelowOne_succ`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_thirty_succ` - closes the IEEE-double square `fl((1 - 536870900 * 2^-53)^2) = 1 - 1073741768 * 2^-53` (`0x1.fffffc0000038p-1`) as the thirtieth predecessor-square cascade step |
| Kahan absolute-value square-31 frontier | Higham Problem 3.11 | `kahanAbsoluteIeeeDoubleTwoBillionOneHundredFortySevenMillionFourHundredEightyThreeThousandFourHundredEightUlpsBelowOne`, `kahanAbsoluteIeeeDouble_square_oneBillionSeventyThreeMillionSevenHundredFortyOneThousandSevenHundredSixtyEightUlpsBelowOne_eq_twoBillionOneHundredFortySevenMillionFourHundredEightyThreeThousandFourHundredEightUlpsBelowOne`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_oneBillionSeventyThreeMillionSevenHundredFortyOneThousandSevenHundredSixtyEightUlpsBelowOne_succ`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_thirtyOne_succ` - closes the IEEE-double square `fl((1 - 1073741768 * 2^-53)^2) = 1 - 2147483408 * 2^-53` (`0x1.fffff800000f0p-1`) as the thirty-first predecessor-square cascade step |
| Kahan absolute-value square-32 frontier | Higham Problem 3.11 | `kahanAbsoluteIeeeDoubleFourBillionTwoHundredNinetyFourMillionNineHundredSixtySixThousandThreeHundredFourUlpsBelowOne`, `kahanAbsoluteIeeeDouble_square_twoBillionOneHundredFortySevenMillionFourHundredEightyThreeThousandFourHundredEightUlpsBelowOne_eq_fourBillionTwoHundredNinetyFourMillionNineHundredSixtySixThousandThreeHundredFourUlpsBelowOne`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_twoBillionOneHundredFortySevenMillionFourHundredEightyThreeThousandFourHundredEightUlpsBelowOne_succ`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_thirtyTwo_succ` - closes the IEEE-double square `fl((1 - 2147483408 * 2^-53)^2) = 1 - 4294966304 * 2^-53` (`0x1.fffff000003e0p-1`) as the thirty-second predecessor-square cascade step |
| Kahan absolute-value square-33 frontier | Higham Problem 3.11 | `kahanAbsoluteIeeeDoubleEightBillionFiveHundredEightyNineMillionNineHundredThirtyThousandFiveHundredSixtyUlpsBelowOne`, `kahanAbsoluteIeeeDouble_square_fourBillionTwoHundredNinetyFourMillionNineHundredSixtySixThousandThreeHundredFourUlpsBelowOne_eq_eightBillionFiveHundredEightyNineMillionNineHundredThirtyThousandFiveHundredSixtyUlpsBelowOne`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_fourBillionTwoHundredNinetyFourMillionNineHundredSixtySixThousandThreeHundredFourUlpsBelowOne_succ`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_thirtyThree_succ` - closes the IEEE-double square `fl((1 - 4294966304 * 2^-53)^2) = 1 - 8589930560 * 2^-53` (`0x1.ffffe00000fc0p-1`) as the thirty-third predecessor-square cascade step |
| Kahan absolute-value square-34 frontier | Higham Problem 3.11 | `kahanAbsoluteIeeeDoubleSeventeenBillionOneHundredSeventyNineMillionEightHundredFiftyTwoThousandNineHundredTwentyEightUlpsBelowOne`, `kahanAbsoluteIeeeDouble_square_eightBillionFiveHundredEightyNineMillionNineHundredThirtyThousandFiveHundredSixtyUlpsBelowOne_eq_seventeenBillionOneHundredSeventyNineMillionEightHundredFiftyTwoThousandNineHundredTwentyEightUlpsBelowOne`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_eightBillionFiveHundredEightyNineMillionNineHundredThirtyThousandFiveHundredSixtyUlpsBelowOne_succ`, `kahanAbsoluteFiniteSquareSteps_ieeeDouble_predOne_thirtyFour_succ` - closes the IEEE-double square `fl((1 - 8589930560 * 2^-53)^2) = 1 - 17179852928 * 2^-53` (`0x1.ffffc00003f80p-1`), recording the thirty-fourth state for optional explicit-model trace work |
| Quadrature sum | Higham Problem 3.12 | `quadratureRule`, `fl_quadrature`, `fl_quadrature_error_bound_of_function_value_rel_error` — separates analytic quadrature error, function-evaluation relative error, and left-to-right dot-product rounding error |
| RandNLA element-wise sampling | Drineas-Mahoney, [Algorithm 1](https://dl.acm.org/doi/10.1145/2842602) | `sqMagTraceProbability_expectationReal_elementwiseTraceSketch_matrix`, `fl_elementwiseTraceSketch_sqMag_error_bound`, `highProbability_sqMagTraceStability_of_markov_budget`, `highProbability_sqMagTraceStability_of_pairwise_chebyshev_budget`, `highProbability_sqMagTraceStability_of_independent_chernoff_budget`, `highProbability_sqMagTraceStability_of_independent_chernoff_optimized_tail_budget` |
| RandNLA element-wise spectral transfer | Drineas-Mahoney, [Algorithm 1 and equation (2)](https://dl.acm.org/doi/10.1145/2842602) | `rectOpNorm2Le`, `elementwiseTraceResidual_eq_sum_sampleResidualIncrement`, `sqMagProb_sum_elementwiseSampleResidualIncrement_entry_eq_zero`, `sqMagProb_sum_elementwiseSampleResidualIncrement_entry_sq_le`, `sqMagProb_sum_vecNorm2Sq_rectMatMulVec_elementwiseSampleResidualIncrement_le`, `sqMagProb_sum_rectSelfAdjointDilation_square_loewnerLe_scalar_id`, `sqMagProb_sum_steps_rectSelfAdjointDilation_square_loewnerLe_scalar_id`, `sqMagProb_sum_finiteTrace_rectSelfAdjointDilation_square_le`, `sqMagProb_sum_steps_finiteTrace_rectSelfAdjointDilation_square_le`, `finiteMatrixExp_smul_finiteIdMatrix`, `finiteTrace_finiteMatrixExp_smul_finiteIdMatrix`, `finiteMatrixExp_symmetric`, `finiteMatrixExp_finiteDiagonal`, `finiteTrace_finiteMatrixExp_finiteDiagonal`, `finiteTrace_finiteHermitianCfcExp_eq_sum_exp_finiteHermitianEigenvalues`, `finiteTrace_finiteMatrixExp_eq_sum_exp_finiteHermitianEigenvalues`, `finiteTrace_finiteMatrixExp_neg_eq_sum_exp_neg_finiteHermitianEigenvalues`, `FiniteProbability.eventProb_exists_finiteHermitianEigenvalue_ge_le_exp_neg_mul_expected_trace_exp`, `FiniteProbability.eventProb_exists_finiteHermitianEigenvalue_ge_le_exp_neg_mul_trace_bound`, `FiniteProbability.eventProb_forall_finiteHermitianEigenvalue_lt_ge_one_sub_exp_neg_mul_expected_trace_exp`, `FiniteProbability.eventProb_forall_finiteHermitianEigenvalue_lt_ge_one_sub_exp_neg_mul_trace_bound`, `FiniteProbability.eventProb_exists_finiteHermitianEigenvalue_le_le_exp_mul_expected_trace_exp_neg`, `FiniteProbability.eventProb_exists_finiteHermitianEigenvalue_le_le_exp_mul_trace_bound`, `FiniteProbability.eventProb_forall_finiteHermitianEigenvalue_gt_ge_one_sub_exp_mul_expected_trace_exp_neg`, `FiniteProbability.eventProb_forall_finiteHermitianEigenvalue_gt_ge_one_sub_exp_mul_trace_bound`, `FiniteProbability.eventProb_forall_abs_finiteHermitianEigenvalue_lt_ge_one_sub_exp_neg_mul_expected_trace_exp_add`, `FiniteProbability.eventProb_forall_abs_finiteHermitianEigenvalue_lt_ge_one_sub_exp_neg_mul_trace_bound_add`, `rectOpNorm2Le_of_selfAdjointDilation_loewnerLe_scalar_id`, `probability_algorithm1_fl_spectral_of_exact_dilation_upper`, `sqMagTraceProbability_expectationReal_elementwiseTraceResidual_frob_sq_le`, `sqMagTraceProbability_eventProb_vecNorm2_rectMatMulVec_elementwiseTraceResidual_le_ge_one_sub`, `sqMagTraceProbability_eventProb_forall_vecNorm2_rectMatMulVec_elementwiseTraceResidual_le_ge_one_sub_sum`, `sqMagTraceProbability_eventProb_fl_vecNorm2_rectMatMulVec_elementwiseTraceResidual_le_ge_one_sub`, `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_ge_one_sub_frob`, `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_ge_one_sub_entrywise`, `fl_elementwiseTraceResidual_rectOpNorm2Le_of_exact`, `probability_algorithm1_fl_spectral_of_exact_spectral`, `sqMagTraceProbability_eventProb_algorithm1FlSpectralRadius_ge_one_sub_delta_frob_explicit_gamma_square` |
| RandNLA row sampling | Drineas-Mahoney, [Algorithm 2, equation (4), and equation (5)](https://dl.acm.org/doi/10.1145/2842602) | `rowSqNormProb`, `ComputedRowScaleDen`, `rowSampleSketchWithComputedDen`, `fl_rowSampleSketchWithComputedDen_error_bound`, `rowSqNormTraceProbability_expectationReal_rowSampleGram_entry`, `rowSqNormTraceProbability_eventProb_rowSampleGram_frob_error_le_epsilon`, `rowSqNormTraceProbability_eventProb_fl_rowSampleGramDot_frob_error_le_epsilon_add_explicit_budget` |
| RandNLA leverage row sampling | Drineas-Mahoney, [Algorithm 2, equation (6), and equation (7)](https://dl.acm.org/doi/10.1145/2842602) | `leverageScoreProb`, `leverage_rowOuterGramSample_mean_eq_id`, `leverage_rowOuterGramSample_finiteLoewnerLe_nat`, `rowSqNormTraceProbability_expectationReal_trace_normed_exp_add_sum_le`, `leverage_rowOuterGramSample_centered_log_cgf_le`, `leverage_rowOuterGramSample_neg_centered_log_cgf_le`, `leverageTraceProbability_eventProb_rowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget`, `leverageTraceProbability_eventProb_fl_rowSampleGramDotWithFlMulThenSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget` |
| RandNLA leverage actual-input row sampling | Drineas-Mahoney, [Algorithm 2, equation (7)](https://dl.acm.org/doi/10.1145/2842602) plus exact analysis factorization \(A=UC\) | `leverageRightGramCongruence`, `leverageFactoredInputSampleGram`, `leverageTraceProbability_eventProb_factoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget`, `leverageFactoredInputDenGramBudget`, `leverage_fl_rowSampleGramDotWithComputedDen_factoredInput_perturb_bound`, `leverageTraceProbability_eventProb_factoredInput_fl_rowSampleGramDotWithFlMulThenSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget` |
| RandNLA leverage stored-basis row sampling | Drineas-Mahoney, [Algorithm 2, equation (7)](https://dl.acm.org/doi/10.1145/2842602) plus Higham-style FP storage/use | `leverageComputedBasisDenGramBudget`, `fl_rowSampleSketchWithComputedBasisDen_abs_error_bound`, `leverage_fl_rowSampleGramDotWithComputedBasisDen_perturb_bound`, `leverageTraceProbability_eventProb_fl_rowSampleGramDotWithStoredBasisMulOneAndFlMulThenSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget`, `leverageTraceProbability_eventProb_fl_rowSampleGramDotWithStoredBasisAddZeroRightAndFlMulThenSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget`, `leverageTraceProbability_eventProb_fl_rowSampleGramDotWithStoredBasisSubZeroRightAndFlMulThenSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget` |
| RandNLA random-projection preconditioning | Drineas-Mahoney, [Algorithm 3](https://dl.acm.org/doi/10.1145/2842602) | `preconditionRows`, `preconditionColumns`, `preconditionElements`, `ComputedPreconditioner`, `ComputedVector`, `ComputedVector.flStoredSign`, `ComputedVector.flStoredSignAddZeroRight`, `ComputedVector.flStoredSignSubZeroRight`, `ComputedMatrix`, `ComputedMatrix.diag`, `ComputedMatrix.flRowSignMul`, `ComputedMatrix.flSqrtInvNatScaledPattern`, `ComputedMatrix.flSqrtInvNatScaledSylvesterPattern`, `ComputedMatrix.flProduct`, `ComputedPreconditioner.flSignedHadamard`, `ComputedPreconditioner.flSignedHadamardExactFactors`, `ComputedPreconditioner.flSignedHadamardScaledPattern`, `ComputedPreconditioner.flSignedHadamardScaledPatternStoredSign`, `ComputedPreconditioner.flSignedHadamardScaledPatternStoredSignAddZeroRight`, `ComputedPreconditioner.flSignedHadamardScaledPatternStoredSignSubZeroRight`, `ComputedPreconditioner.flSignedHadamardSylvesterPattern`, `ComputedPreconditioner.flSignedHadamardSylvesterFhtSchedule`, `ComputedPreconditioner.flSignedHadamardSylvesterPatternStoredSign`, `ComputedPreconditioner.flSignedHadamardSylvesterPatternStoredSignAddZeroRight`, `ComputedPreconditioner.flSignedHadamardSylvesterPatternStoredSignSubZeroRight`, `HadamardSignPattern`, `sylvesterHadamardSignPattern`, `hadamardFlat_sqrt_inv_nat_mul_signPattern`, `hadamardFlat_sqrt_inv_nat_mul_sylvesterSignPattern`, `basisColumnProjector`, `ComputedPreconditioner.flBasisColumnProjector`, `ComputedUniformRowScaleDen`, `ComputedUniformRowScaleDen.flSqrtExactInput`, `ComputedUniformRowScaleDen.flDivThenSqrt`, `ComputedUniformRowScaleDen.flInvMulThenSqrt`, `ComputedUniformRowScaleDen.flSqrtDivSqrt`, `ComputedUniformRowScaleDen.flSqrtMulInvSqrt`, `uniformRowFlSqrtMulInvSqrtScaleDen`, `fl_computedMatrixProduct_total_error_bound`, `flComputedMatrixProductEntryErrorBudget`, `fhtButterflyExact`, `flFhtButterfly`, `flFhtButterfly_add_error_bound`, `flFhtButterfly_sub_error_bound`, `fhtPairUpdateExact`, `flFhtPairUpdate`, `fhtPairUpdateErrorBudget`, `flFhtPairUpdate_error_bound`, `fhtPairUpdatePropagatedErrorBudget`, `flFhtPairUpdate_propagated_error_bound`, `fhtPairScheduleExact`, `flFhtPairSchedule`, `fhtPairSchedulePropagatedErrorBudget`, `flFhtPairSchedule_propagated_error_bound`, `fhtScaledPairScheduleExact`, `flFhtScaledPairSchedule`, `fhtScaledPairScheduleErrorBudget`, `flFhtScaledPairSchedule_error_bound`, `fl_preconditionRowsWithComputedLeft_total_error_bound`, `fl_preconditionRowsWithComputedLeftAndInput_total_error_bound`, `flPreconditionRowsWithComputedLeftEntryErrorBudget`, `flPreconditionRowsWithComputedLeftInputEntryErrorBudget`, `fl_preconditionRowsWithComputedLeftInput_entry_error_budget_bound`, `fl_basisColumnProjector_total_error_bound`, `flBasisColumnProjectorEntryErrorBudget`, `fl_preconditionColumnsWithComputedRight_total_error_bound`, `fl_preconditionElementsWithComputed_total_error_bound`, `fl_preconditionElementsWithComputedBasisProjectors_total_error_bound`, `fl_uniformRowSampleSketch_computedDen_error_bound`, `fl_uniformRowSampleSketch_computedDen_total_error_bound`, `uniformRowSampleGram_frob_error_bound_of_basis_entrywise_abs`, `signedHadamardScaledPatternPreconditioner`, `signedHadamardScaledPatternStoredSignPreconditioner`, `signedHadamardScaledPatternStoredSignAddZeroRightPreconditioner`, `signedHadamardScaledPatternStoredSignSubZeroRightPreconditioner`, `signedHadamardSylvesterPatternPreconditioner`, `signedHadamardSylvesterFhtSchedulePreconditioner`, `signedHadamardSylvesterFhtScheduleStoredSignPreconditioner`, `signedHadamardSylvesterPatternStoredSignPreconditioner`, `signedHadamardSylvesterPatternStoredSignAddZeroRightPreconditioner`, `signedHadamardSylvesterPatternStoredSignSubZeroRightPreconditioner`, `signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one`, `signedHadamardUniformRowTraceProbability_eventProb_computedLeftInputPreconditioned_fl_uniformRowPerturbEvent_eq_one`, `signedHadamardUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one`, `signedHadamardUniformRowTraceProbability_eventProb_scaledPatternComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one`, `signedHadamardUniformRowTraceProbability_eventProb_scaledPatternStoredSignComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one`, `signedHadamardUniformRowTraceProbability_eventProb_scaledPatternStoredSignAddZeroRightComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one`, `signedHadamardUniformRowTraceProbability_eventProb_scaledPatternStoredSignSubZeroRightComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one`, `signedHadamardUniformRowTraceProbability_eventProb_sylvesterPatternComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one`, `signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one`, `signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one`, `signedHadamardUniformRowTraceProbability_eventProb_sylvesterPatternStoredSignComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one`, `signedHadamardUniformRowTraceProbability_eventProb_sylvesterPatternStoredSignAddZeroRightComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one`, `signedHadamardUniformRowTraceProbability_eventProb_sylvesterPatternStoredSignSubZeroRightComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one`, `preconditionElements_frobNorm_orthogonal`, `preconditionElements_hasOrthonormalColumns_of_orthogonal`, `signedOrthogonalPreconditionRows_hasOrthonormalColumns`, `rademacherTraceProbability_eventProb_forall_leverageScoreProb_signedHadamard_le_log_delta_ge_one_sub_delta`, `signedHadamardUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess`, `signedHadamardUniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_constBudget_srht_log_preprocess`, `signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_constBudget_srht_log_preprocess`, `signedHadamardUniformRowTraceProbability_eventProb_scaledPatternStoredSignComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess` |
| RandNLA least-squares sketch objective | Drineas-Mahoney, [equation (8)](https://dl.acm.org/doi/10.1145/2842602) | `lsObjective`, `PreservesLSObjective`, `preservesLSObjective_of_coordinate_finiteLoewner_error`, `leverageTraceProbability_eventProb_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget`, `leverageTraceProbability_eventProb_fl_lsObjective_le_one_add_eta_of_augmentedSpan_sample_budget`, `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error`, `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_solver_gap`, `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_forward_error`, `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_perturbed_gram_solver`, `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_ls_qr_backward_error_solver`, `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_offDiagonalControl_solver`, `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_sourceOffDiagonalControl_solver`, `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_solver`, `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_kappaInf_dualBudget_solver`, `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_solver`, `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_kappaInf_dualBudget_solver`, `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_kappaInf_dualBudget_solver`, `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_kappaInf_dualBudget_solver_of_horizonBudget`, `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver`, `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver_of_horizonBudget`, `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver_of_actualUnitRoundoff_no_gammaValid_of_horizonBudget`, `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver`, `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver_of_horizonBudget`, `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver_of_actualUnitRoundoff_no_gammaValid`, `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver_of_actualUnitRoundoff_no_gammaValid_of_horizonBudget`, `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSmallness_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver`, `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSmallness_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_concreteDual_solver`, `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver`, `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_globalProduct_kappaInf_dualBudget_solver`, `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_normal_eq_cholesky_solver` |
| RandNLA low-rank approximation foundations | Drineas-Mahoney, equation (9) | `RectRankFactorization`, `RectRankAtMost`, `lowRankResidualFrob`, `IsBestRankApproxFrob`, `rightBasisProjectorApprox`, `leftBasisProjectorApprox`, `columnSketch`, `LeftFactorThrough`, `Equation9ResidualCertificate`, `columnSketchLeftMultiplier`, `columnSketchRightMultiplier`, `columnSketchGram`, `columnSketchGramInverseCoefficient`, `ColumnSketchGramInverseCertificate`, `ColumnSketchGeneralizedInverse`, `ColumnSketchOrthogonalProjectorCertificate`, `ColumnSketchMoorePenroseCertificate` | `rightBasisProjectorApproxFactorization`, `leftBasisProjectorApproxFactorization`, `rightBasisProjectorApprox_rankAtMost`, `leftBasisProjectorApprox_rankAtMost`, `IsBestRankApproxFrob.residual_le_of_rankAtMost`, `IsBestRankApproxFrob.residual_le_rightBasisProjectorApprox`, `IsBestRankApproxFrob.residual_le_leftBasisProjectorApprox`, `preconditionRows_rankAtMost_of_leftFactorThrough`, `sketchColumnProjectorApprox_rankAtMost`, `Equation9ResidualCertificate.tail_add_coupling_nonneg`, `equation9RankResidualSurface`, `equation9RelativeResidualSurface`, `columnSketchLeftMultiplier_leftFactorThrough`, `columnSketchLeftMultiplier_rankAtMost`, `columnSketchLeftMultiplier_equation9RankResidualSurface`, `columnSketchLeftMultiplier_equation9RelativeResidualSurface`, `columnSketchLeftMultiplier_reproducesSketch_of_generalizedInverse`, `columnSketchLeftMultiplier_idempotent_of_generalizedInverse`, `columnSketchLeftMultiplier_projectorSurface_of_generalizedInverse`, `columnSketchLeftMultiplier_symmetric_of_orthogonalProjectorCertificate`, `columnSketchLeftMultiplier_idempotent_of_orthogonalProjectorCertificate`, `columnSketchLeftMultiplier_orthogonalProjectorSurface`, `ColumnSketchMoorePenroseCertificate.to_generalizedInverse`, `ColumnSketchMoorePenroseCertificate.to_orthogonalProjectorCertificate`, `columnSketchRightMultiplier_reproducesCoeff_of_moorePenroseCertificate`, `columnSketchRightMultiplier_symmetric_of_moorePenroseCertificate`, `columnSketchLeftMultiplier_orthogonalProjectorSurface_of_moorePenroseCertificate`, `columnSketchRightMultiplier_eq_id_of_gramInverseCertificate`, `columnSketchGramInverseCoefficient_reproducesCoeff`, `columnSketchLeftMultiplier_symmetric_of_gramInverseCertificate`, `columnSketchRightMultiplier_symmetric_of_gramInverseCertificate`, `columnSketchGramInverseCoefficient_generalizedInverse`, `columnSketchGramInverseCoefficient_moorePenroseCertificate`, `columnSketchLeftMultiplier_orthogonalProjectorSurface_of_gramInverseCertificate` |
| RandNLA low-rank norm-generic equation (9) surface | Drineas-Mahoney, equation (9) | `RectNormLike`, `lowRankResidualNorm`, `IsBestRankApproxNorm`, `Equation9ResidualNormCertificate`, `Equation9HeadTailSketchNormCertificate` | `IsBestRankApproxNorm.residual_le_of_rankAtMost`, `Equation9HeadTailSketchNormCertificate.to_residualNormCertificate`, `Equation9ResidualNormCertificate.tail_add_coupling_nonneg`, `equation9RankResidualNormSurface`, `equation9RelativeResidualNormSurface`, `equation9HeadTailSketchNormRankResidualSurface`, `equation9HeadTailSketchNormRelativeResidualSurface` |
| RandNLA low-rank Frobenius norm bridge for equation (9) | Drineas-Mahoney, equation (9) | `frobRectNormLike`, `frobRectNormLike_norm`, `lowRankResidualNorm_frobRectNormLike`, `IsBestRankApproxFrob.to_norm_frobRectNormLike`, `Equation9ResidualCertificate.to_norm_frobRectNormLike`, `Equation9HeadTailSketchCertificate.to_norm_frobRectNormLike` | `frobRectNormLike_orthogonal_left`, `frobRectNormLike_orthogonal_right`, `equation9HeadTailSketchFrobNormRankResidualSurface`, `equation9HeadTailSketchFrobNormRelativeResidualSurface` |
| RandNLA low-rank unitarily invariant norm API | Drineas-Mahoney, equation (9) | `UnitaryInvariantRectNormLike`, Frobenius unitary instance, and unitary-norm equation-(9) wrappers | `UnitaryInvariantRectNormLike.norm_matMulRectLeft`, `UnitaryInvariantRectNormLike.norm_matMulRectRight`, `frobUnitaryInvariantRectNormLike`, `equation9HeadTailSketchUnitaryNormRelativeResidualSurface` |
| RandNLA low-rank determinant Gram route | Drineas-Mahoney, equation (9) | `nonsingInv_symmetric_of_symmetric`, `columnSketchGram_symmetric`, `columnSketchGramInverseCertificate_of_det_ne_zero` | `columnSketchGramInverseCoefficient_moorePenroseCertificate_of_det_ne_zero`, `columnSketchLeftMultiplier_orthogonalProjectorSurface_of_det_ne_zero` |
| RandNLA low-rank thin-factor Gram route | Drineas-Mahoney, equation (9) | `ColumnSketchThinFactorCertificate` | `columnSketchGram_eq_factorGram_of_thinFactorCertificate`, `columnSketchGram_det_ne_zero_of_thinFactorCertificate`, `columnSketchGramInverseCertificate_of_thinFactorCertificate`, `columnSketchGramInverseCoefficient_moorePenroseCertificate_of_thinFactorCertificate`, `columnSketchLeftMultiplier_orthogonalProjectorSurface_of_thinFactorCertificate` |
| RandNLA low-rank source-SVD head rank certificate | Drineas-Mahoney, equation (9) | Exact source head `U Sigma V^T` with displayed source factors | `sourceSVDFactorMatrixRankFactorization`, `sourceSVDFactorMatrix_rankAtMost` |
| RandNLA low-rank source-split best-rank handoff | Drineas-Mahoney, equation (9) | Exact source split `A = U Sigma V^T + Tail` plus supplied tail-optimality inequality | `lowRankResidualFrob_sourceSVDFactorMatrix_eq_tail`, `lowRankResidualNorm_sourceSVDFactorMatrix_eq_tail`, `sourceSVDFactorMatrix_isBestRankApproxFrob_of_tail_optimal`, `sourceSVDFactorMatrix_isBestRankApproxNorm_of_tail_optimal` |
| RandNLA low-rank source-SVD Gram route | Drineas-Mahoney, equation (9) | `sourceSVDFactorMatrix`, `rightSketchCrossGram`, `sourceSVDSketchRightFactor`, `columnSketchThinFactorCertificate_of_sourceSVD_det_factors` | `sourceSVDSketchRightFactor_det_ne_zero_of_det_ne_zero`, `columnSketchGram_det_ne_zero_of_sourceSVD_det_factors`, `columnSketchGramInverseCertificate_of_sourceSVD_det_factors`, `columnSketchGramInverseCoefficient_moorePenroseCertificate_of_sourceSVD_det_factors`, `columnSketchLeftMultiplier_orthogonalProjectorSurface_of_sourceSVD_det_factors` |
| RandNLA low-rank head-tail residual route | Drineas-Mahoney, equation (9) | `frobNormRect_neg`, `frobNormRect_sub_le`, `ColumnSketchHeadFactorization`, `Equation9HeadTailSketchCertificate`, `columnSketchGramInverseProjector` | `preconditionRows_reproduces_head_of_columnSketchHeadFactorization`, `Equation9HeadTailSketchCertificate.to_residualCertificate`, `equation9HeadTailSketchRankResidualSurface`, `equation9HeadTailSketchRelativeResidualSurface`, `columnSketchGramInverseProjector_orthogonalProjectorSurface_of_sourceSVD_det_factors`, `columnSketchGramInverseProjector_sourceSVD_headTailRankResidualSurface`, `columnSketchGramInverseProjector_sourceSVD_headTailRelativeResidualSurface` |
| RandNLA low-rank explicit-coefficient residual route | Drineas-Mahoney, equation (9) | `columnSketchHead`, `columnSketchTail`, `columnSketchHead_headFactorization`, `columnSketchHeadTail_split` | `equation9HeadTailSketchCertificate_of_columnSketchHead`, `columnSketchGramInverseProjector_sourceSVD_columnSketchHeadRankResidualSurface`, `columnSketchGramInverseProjector_sourceSVD_columnSketchHeadRelativeResidualSurface` |
| RandNLA low-rank source-coefficient residual route | Drineas-Mahoney, equation (9) | `sourceSketchCoefficient`, `sourceSketchResidualTail` | `rightSketchCrossGram_sourceSketchCoefficient`, `sourceSVDSketchRightFactor_sourceSketchCoefficient`, `columnSketchHead_sourceSVDFactorMatrix_sourceSketchCoefficient`, `columnSketchHead_sourceHeadTail_sourceSketchCoefficient`, `columnSketchTail_sourceHeadTail_sourceSketchCoefficient`, `equation9RankResidualSurface_of_sourceHeadTail_sourceSketchCoefficient`, `equation9RelativeResidualSurface_of_sourceHeadTail_sourceSketchCoefficient` |
| RandNLA low-rank source-coefficient Moore-Penrose route | Drineas-Mahoney, equation (9) | `ColumnSketchMoorePenroseCertificate`, `sourceSketchResidualTail` | `columnSketchLeftMultiplier_sourceHeadTail_sourceSketchCoefficientRankResidualSurface`, `columnSketchLeftMultiplier_sourceHeadTail_sourceSketchCoefficientRelativeResidualSurface` |
| RandNLA low-rank source-coefficient Gram-inverse route | Drineas-Mahoney, equation (9) | `columnSketchGramInverseProjector`, `sourceSketchResidualTail` | `columnSketchGramInverseProjector_sourceHeadTail_sourceSketchCoefficientRankResidualSurface_of_det_ne_zero`, `columnSketchGramInverseProjector_sourceHeadTail_sourceSketchCoefficientRelativeResidualSurface_of_det_ne_zero` |
| RandNLA low-rank source-tail orthogonality from tail factors | Drineas-Mahoney, equation (9) | Exact tail factorization `Tail=U_tail Sigma_tail V_tail^T` and left-basis cross-orthogonality `U^T U_tail=0` | `sourceTailLeftOrthogonal_of_tail_factor_left_cross_zero` |
| RandNLA low-rank source head-tail Gram split | Drineas-Mahoney, equation (9) | `sourceTailLeftOrthogonal`, `columnSketch_sourceSVDFactorMatrix` | `columnSketch_sourceSVDFactorMatrix_tail_leftOrthogonal`, `columnSketch_tail_sourceSVDFactorMatrix_leftOrthogonal`, `columnSketchGram_sourceHeadTail_leftOrthogonal` |
| RandNLA low-rank Gram PSD determinant bridge | Drineas-Mahoney, equation (9) | `finiteQuadraticForm_columnSketchGram_eq_sum_sq`, `columnSketchGram_finitePSD` | `matrix_det_ne_zero_of_posDef_add_posSemidef`, `columnSketchGram_sourceHeadTail_det_ne_zero_of_head_posDef` |
| RandNLA low-rank source determinant PosDef bridge | Drineas-Mahoney, equation (9) | `matrix_transpose_mul_self_posDef_of_det_ne_zero`, `columnSketchGram_posDef_of_thinFactorCertificate` | `columnSketchGram_posDef_of_sourceSVD_det_factors`, `columnSketchGram_sourceHeadTail_det_ne_zero_of_sourceSVD_det_factors` |
| RandNLA low-rank tail-factor determinant route | Drineas-Mahoney, equation (9) | Exact tail factorization plus `U^T U_tail=0`, `U^T U=I`, `det(Sigma) != 0`, `det(V^T Z) != 0` | `columnSketchGram_sourceHeadTail_det_ne_zero_of_sourceSVD_det_factors_tail_factor_left_cross_zero` |
| RandNLA low-rank diagonal singular-block determinant route | Drineas-Mahoney, equation (9) | Exact diagonal `Sigma`, nonzero or positive displayed singular values, exact tail factorization, `U^T U_tail=0`, `U^T U=I`, `det(V^T Z) != 0` | `matrix_det_ne_zero_of_eq_diagonal_nonzero`, `matrix_det_ne_zero_of_eq_diagonal_pos`, `columnSketchGram_sourceHeadTail_det_ne_zero_of_sourceSVD_diagonal_tail_factor_left_cross_zero` |
| RandNLA low-rank diagonal source-SVD sketch/projector route | Drineas-Mahoney, equation (9) | Exact diagonal `Sigma`, nonzero or positive displayed singular values, `U^T U=I`, `det(V^T Z) != 0`, optional source-tail orthogonality | `sourceSVDSketchRightFactor_det_ne_zero_of_diagonal_nonzero`, `columnSketchThinFactorCertificate_of_sourceSVD_diagonal_det_factors`, `columnSketchGram_posDef_of_sourceSVD_diagonal_det_factors`, `columnSketchGramInverseProjector_orthogonalProjectorSurface_of_sourceSVD_diagonal_det_factors` |
| RandNLA low-rank diagonal source-SVD residual surfaces | Drineas-Mahoney, equation (9) | Exact diagonal `Sigma`, nonzero displayed singular values, exact source-tail orthogonality when a tail is present, `det(V^T Z) != 0`, supplied tail/coupling radii | `columnSketchGramInverseProjector_sourceSVD_diagonal_headTailRankResidualSurface`, `columnSketchGramInverseProjector_sourceSVD_diagonal_columnSketchHeadRelativeResidualSurface`, `columnSketchGramInverseProjector_sourceHeadTail_sourceSketchCoefficientRelativeResidualSurface_of_sourceSVD_diagonal_det_factors` |
| RandNLA low-rank diagonal source-SVD scalar tail-rate surfaces | Drineas-Mahoney, equation (9) | Exact diagonal head singular block, exact tail factorization `T=U_tail Sigma_tail V_perp^T`, exact left/right orthogonality, `det(V^T Z) != 0`, and supplied exact cross-term radius | `columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_sourceSVD_diagonal_crossTerm`, `columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_sourceSVD_diagonal_crossTerm` |
| RandNLA low-rank diagonal source-SVD tail-optimal relative rate | Drineas-Mahoney, equation (9) | LR.1bm hypotheses plus supplied Frobenius tail-optimality inequality for the exact source head | `columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_sourceSVD_diagonal_crossTerm_tailOptimal` |
| RandNLA low-rank diagonal source-SVD certificate handoff | Drineas-Mahoney, equation (9) | `DiagonalSourceSVDTailCertificate` packages the exact source split, exact tail factorization, diagonal nonzero head block, and left/right orthogonality/completeness fields; probabilities/laws remain exact | `DiagonalSourceSVDTailCertificate.sourceTailLeftOrthogonal`, `DiagonalSourceSVDTailCertificate.isBestRankApproxFrob_of_tail_optimal`, `columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_diagonalSourceSVDTailCertificate`, `columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_diagonalSourceSVDTailCertificate` |
| RandNLA low-rank block source-SVD certificate constructor | Drineas-Mahoney, equation (9) | Exact block decomposition `A=U Sigma_h V^T+U_tail Sigma_tail V_perp^T`, exact `[U,U_tail]` and `[V_perp,V]` block orthonormality/completeness, diagonal nonzero head block; probabilities/laws remain exact | `leftBasisBlock_component_orthonormal_fields_of_col_orthonormal`, `BlockDiagonalSourceSVDTailCertificate.to_diagonalSourceSVDTailCertificate`, `columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_blockDiagonalSourceSVDTailCertificate`, `columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_blockDiagonalSourceSVDTailCertificate` |
| RandNLA low-rank square-SVD split certificate constructor | Drineas-Mahoney, equation (9) | Exact square SVD-style tables `Ufull`, `Vfull`, `sigma` split into head/tail source blocks by `Fin.castAdd`/`Fin.natAdd`; probabilities/laws remain exact | `squareSVDHeadLeft`, `squareSVDTailLeft`, `squareSVDHeadRight`, `squareSVDTailRight`, `squareSVDHeadDiagonal`, `squareSVDTailDiagonal`, `sourceSVDFactorMatrix_squareSVDHeadDiagonal`, `sourceSVDFactorMatrix_squareSVDTailDiagonal`, `BlockDiagonalSourceSVDTailCertificate.of_squareSVD`, `columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_squareSVD`, `columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_squareSVD` |
| RandNLA low-rank rectangular-thin SVD split certificate constructor | Drineas-Mahoney, equation (9) | Exact thin left table with orthonormal columns, exact full right orthogonal table, exact representation `A=Ufull diag(sigma) Vfull^T`, and head/tail source split; probabilities/laws remain exact | `rectangularThinSVDHeadLeft`, `rectangularThinSVDTailLeft`, `sourceSVDFactorMatrix_rectangularThinSVDHeadDiagonal`, `sourceSVDFactorMatrix_rectangularThinSVDTailDiagonal`, `BlockDiagonalSourceSVDTailCertificate.of_rectangularThinSVD`, `columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_rectangularThinSVD`, `columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectangularThinSVD` |
| RandNLA low-rank head-positive SVD split constructors | Drineas-Mahoney, equation (9) | Strictly positive displayed head singular entries feed the square and thin-rectangular split constructors without a separate raw nonzero-head hypothesis; probabilities/laws remain exact | `squareSVDHeadValues_pos`, `squareSVDHeadValues_nonzero_of_pos`, `BlockDiagonalSourceSVDTailCertificate.of_squareSVD_head_pos`, `BlockDiagonalSourceSVDTailCertificate.of_rectangularThinSVD_head_pos`, `columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_squareSVD_head_pos`, `columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_squareSVD_head_pos`, `columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_rectangularThinSVD_head_pos`, `columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectangularThinSVD_head_pos` |
| RandNLA low-rank source-SVD tail norm identity | Drineas-Mahoney, equation (9) | Exact source factors with orthonormal left/right columns preserve the Frobenius norm of the displayed singular-value block; probabilities/laws remain exact | `frobNormSqRect_sourceSVDFactorMatrix_orthonormal`, `frobNormRect_sourceSVDFactorMatrix_orthonormal`, `BlockDiagonalSourceSVDTailCertificate.tail_frobNorm_eq_sigma`, `BlockDiagonalSourceSVDTailCertificate.tail_lowRankResidual_eq_sigma`, `columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_blockDiagonalSourceSVDTailCertificate_sigmaTail` |
| RandNLA low-rank square/thin SVD sigma-tail wrappers | Drineas-Mahoney, equation (9) | Supplied square and thin-rectangular SVD-style tables inherit the sigma-tail norm/residual identity and relative wrappers stated with `||squareSVDTailDiagonal sigma||_F`; probabilities/laws remain exact | `frobNormRect_squareSVDTail_eq_sigmaTail`, `lowRankResidualFrob_squareSVDHead_eq_sigmaTail`, `columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_squareSVD_sigmaTail`, `columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_squareSVD_head_pos_sigmaTail`, `frobNormRect_rectangularThinSVDTail_eq_sigmaTail`, `lowRankResidualFrob_rectangularThinSVDHead_eq_sigmaTail`, `columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectangularThinSVD_sigmaTail`, `columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectangularThinSVD_head_pos_sigmaTail` |
| RandNLA low-rank square/thin SVD best-rank handoff | Drineas-Mahoney, equation (9) | Supplied square and thin-rectangular SVD-style tables become `IsBestRankApproxFrob` certificates from a visible sigma-tail optimality inequality; probabilities/laws remain exact | `isBestRankApproxFrob_of_squareSVD_sigmaTail_optimal`, `isBestRankApproxFrob_of_squareSVD_head_pos_sigmaTail_optimal`, `isBestRankApproxFrob_of_rectangularThinSVD_sigmaTail_optimal`, `isBestRankApproxFrob_of_rectangularThinSVD_head_pos_sigmaTail_optimal` |
| RandNLA low-rank rank-nullity kernel foundation | Drineas-Mahoney, equation (9) | Any exact `RectRankAtMost m (r+1) r` competitor has a nonzero right-kernel vector on `r+1` coordinates; probabilities/laws remain exact | `rectRankFactorization_exists_rightKernelVector_succ`, `rectRankAtMost_exists_rightKernelVector_succ` |
| RandNLA low-rank q-dimensional right-kernel foundation | Drineas-Mahoney, equation (9) | The exact right factor of any rank-`r` competitor on `r+q` coordinates has kernel dimension at least `q`, and right-factor kernel vectors annihilate the represented matrix; probabilities/laws remain exact | `rectRankRightFactorMap`, `rectRankRightFactorMap_ker_finrank_ge`, `rectRankFactorization_rightKernel_finrank_ge`, `rectRankFactorization_matrix_rightKernel_of_rightFactor_ker` |
| RandNLA low-rank q-dimensional right-kernel family | Drineas-Mahoney, equation (9) | Select a `Fin q` linearly independent family inside the right-factor kernel of an exact rank-`r` competitor and prove every selected vector annihilates the represented matrix; probabilities/laws remain exact | `rectRankFactorization_exists_rightKernelFamily` |
| RandNLA low-rank q-dimensional orthonormal right-kernel family | Drineas-Mahoney, equation (9) | Select a `Fin q` orthonormal family inside the Euclidean-coordinate right-factor kernel and prove every selected vector annihilates the represented matrix; probabilities/laws remain exact | `rectRankRightFactorEuclideanMap`, `rectRankRightFactorEuclideanMap_ker_finrank_ge`, `rectRankFactorization_euclideanRightKernel_finrank_ge`, `rectRankFactorization_matrix_rightKernel_of_euclideanRightFactor_ker`, `rectRankFactorization_exists_orthonormalRightKernelFamily` |
| RandNLA low-rank orthonormal right-kernel residual energy | Drineas-Mahoney, equation (9) | Bessel/Frobenius domination for exact orthonormal right probes, plus the LR.1di right-kernel residual-energy adapter; probabilities/laws remain exact | `sum_vecNorm2Sq_rectMatMulVec_le_frobNormSqRect_of_orthonormal`, `sum_vecNorm2Sq_rectMatMulVec_lowRankResidual_le_of_orthonormal_rightKernel`, `rectRankFactorization_exists_orthonormalRightKernelFamily_energy_le` |
| RandNLA low-rank diagonal source-tail energy under a gap | Drineas-Mahoney, equation (9) | Exact diagonal mass-transfer lower bound for an orthonormal `q`-frame: head diagonal squares above `eta` and tail squares below `eta` force the diagonal source action to dominate the displayed tail-energy sum; probabilities/laws remain exact | `headTail_weighted_tail_sum_le_of_gap`, `orthonormal_sum_coord_sq_le_one`, `orthonormal_sum_coord_sq_eq_card`, `sum_vecNorm2Sq_diagonal_rectMatMulVec_eq_weighted_coord_sq`, `sum_vecNorm2Sq_diagonal_rectMatMulVec_ge_tail_sq_of_orthonormal_gap` |
| RandNLA low-rank ordered diagonal source-tail energy | Drineas-Mahoney, equation (9) | Exact positive-head ordered-diagonal instantiation: an antitone table of displayed diagonal squares supplies the LR.1dk head-tail gap and hence the source-tail energy lower bound; probabilities/laws remain exact | `diagonal_headTail_square_gap_of_antitone_head_pos`, `sum_vecNorm2Sq_diagonal_rectMatMulVec_ge_tail_sq_of_orthonormal_antitone_head_pos` |
| RandNLA low-rank zero-head diagonal source-tail energy | Drineas-Mahoney, equation (9) | Exact zero-head companion: a full orthonormal `q`-frame has coordinate-square mass one, so diagonal source energy equals the displayed tail square sum; probabilities/laws remain exact | `orthonormal_sum_coord_sq_eq_one_of_card_eq`, `orthonormal_sum_coord_sq_eq_one_of_full`, `sum_vecNorm2Sq_diagonal_rectMatMulVec_eq_sum_sq_of_orthonormal_full`, `sum_vecNorm2Sq_diagonal_rectMatMulVec_ge_tail_sq_of_orthonormal_zero_head` |
| RandNLA low-rank combined ordered diagonal source-tail energy | Drineas-Mahoney, equation (9) | Exact ordered-diagonal theorem for all head counts: split internally into the positive-head gap case and the zero-head full-frame equality; probabilities/laws remain exact | `sum_vecNorm2Sq_diagonal_rectMatMulVec_ge_tail_sq_of_orthonormal_antitone` |
| RandNLA low-rank source-factor ordered source-tail energy | Drineas-Mahoney, equation (9) | Exact `U diag(sigma) V^T` transport of the q-frame ordered diagonal theorem: right orthogonality preserves the probe frame and left column orthonormality preserves squared source action; probabilities/laws remain exact | `inner_matTranspose_mulVec_eq_of_isOrthogonal`, `orthonormal_matTranspose_mulVec_of_isOrthogonal`, `vecNorm2Sq_sourceSVDFactorMatrix_eq_diagonal_transpose_action`, `sum_vecNorm2Sq_sourceSVDFactorMatrix_ge_tail_sq_of_orthonormal_antitone` |
| RandNLA low-rank source-factor gap lower-bound bridge | Drineas-Mahoney, equation (9) | Exact `U diag(sigma) V^T` transport and q-dimensional residual lower bound under a visible head-tail gap, avoiding a sorted-tail assumption for constructed complement-tail enumerations; probabilities/laws remain exact | `sum_vecNorm2Sq_sourceSVDFactorMatrix_ge_tail_sq_of_orthonormal_gap`, `rectRankAtMost_lowRankResidualFrob_sq_ge_tail_sum_of_sourceSVDFactorMatrix_gap`, `sqrt_tail_sum_le_lowRankResidualFrob_of_sourceSVDFactorMatrix_gap` |
| RandNLA low-rank q-dimensional Eckart-Young lower-bound bridge | Drineas-Mahoney, equation (9) | Exact supplied-source-factor lower bound: every rank-at-most-`r` competitor has residual Frobenius square at least the displayed ordered tail-square sum, with a square-root norm form; probabilities/laws remain exact | `rectRankAtMost_lowRankResidualFrob_sq_ge_tail_sum_of_sourceSVDFactorMatrix_antitone`, `sqrt_tail_sum_le_lowRankResidualFrob_of_sourceSVDFactorMatrix_antitone` |
| RandNLA low-rank ordered supplied-SVD best-rank adapter | Drineas-Mahoney, equation (9) | Exact square and thin supplied-SVD tables with antitone singular-square entries supply the sigma-tail optimality inequality and hence `IsBestRankApproxFrob` for the displayed head; probabilities/laws remain exact | `sourceSVDFactorMatrix_diagonal_eq_sum`, `squareSVD_sigmaTail_le_lowRankResidualFrob_of_antitone`, `isBestRankApproxFrob_of_squareSVD_antitone`, `isBestRankApproxFrob_of_squareSVD_head_pos_antitone`, `rectangularThinSVD_sigmaTail_le_lowRankResidualFrob_of_antitone`, `isBestRankApproxFrob_of_rectangularThinSVD_antitone`, `isBestRankApproxFrob_of_rectangularThinSVD_head_pos_antitone` |
| RandNLA low-rank ordered supplied-SVD relative surfaces | Drineas-Mahoney, equation (9) | Exact square and thin supplied-SVD scalar tail-rate relative surfaces use antitone singular-square entries instead of a raw tail-optimality hypothesis; probabilities/laws remain exact | `columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_squareSVD_sigmaTail_antitone`, `columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_squareSVD_head_pos_sigmaTail_antitone`, `columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectangularThinSVD_sigmaTail_antitone`, `columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectangularThinSVD_head_pos_sigmaTail_antitone` |
| RandNLA low-rank min-max residual lower-bound adapter | Drineas-Mahoney, equation (9) | A supplied exact vector-action lower bound on an `r+1` right-coordinate source block forces every rank-at-most-`r` competitor to have Frobenius residual at least that bound; probabilities/laws remain exact | `rectMatMulVec_sub_eq_left_of_rightKernel`, `rectRankAtMost_lowRankResidualFrob_ge_of_vector_lower_bound_succ` |
| RandNLA low-rank diagonal source-action lower bound | Drineas-Mahoney, equation (9) | Exact left-orthonormal columns, an exact square orthogonal right block, and diagonal singular entries bounded below by `sigma` supply the vector-action lower bound used by the min-max adapter; probabilities/laws remain exact | `vecNorm2Sq_leftOrthonormalFactor`, `vecNorm2Sq_diagonal_lower_bound`, `rectMatMulVec_sourceSVDFactorMatrix`, `sourceSVDFactorMatrix_diagonal_vector_action_lower_bound` |
| RandNLA low-rank supplied SVD diagonal lower-action wrappers | Drineas-Mahoney, equation (9) | Supplied exact square and thin-rectangular SVD-style diagonal factors instantiate the source-action lower bound when every displayed singular entry is at least `sigma`; probabilities/laws remain exact | `squareSVD_diagonal_vector_action_lower_bound`, `rectangularThinSVD_diagonal_vector_action_lower_bound` |
| RandNLA low-rank supplied SVD residual lower-bound wrappers | Drineas-Mahoney, equation (9) | Supplied exact square and thin-rectangular diagonal source blocks on `r+1` right coordinates force rank-at-most-`r` competitors to have Frobenius residual at least `sigma`; probabilities/laws remain exact | `rectRankAtMost_lowRankResidualFrob_ge_of_squareSVD_diagonal_succ`, `rectRankAtMost_lowRankResidualFrob_ge_of_rectangularThinSVD_diagonal_succ` |
| RandNLA low-rank ordered right-Gram head residual lower bound | Drineas-Mahoney, equation (9) | The constructed exact ordered top-`r+1` right-Gram head coefficient block has residual at least the last selected ordered singular value against every rank-at-most-`r` competitor; probabilities/laws remain exact | `rectRankAtMost_lowRankResidualFrob_ge_of_rectRightGramOrderedHeadDiagonal_succ` |
| RandNLA low-rank ordered one-step best-rank coefficient block | Drineas-Mahoney, equation (9) | The constructed exact ordered top-`r+1` right-Gram coefficient block has its first-`r` truncation as a Frobenius best rank-`r` approximant; probabilities/laws remain exact | `frobNorm_squareSVDTailDiagonal_one`, `isBestRankApproxFrob_of_rectRightGramOrderedHeadDiagonal_succ` |
| RandNLA low-rank multi-tail diagonal Frobenius identity | Drineas-Mahoney, equation (9) | The displayed exact `q`-tail diagonal Frobenius square is the sum of the selected tail singular-value squares; probabilities/laws remain exact | `frobNormSq_squareSVDTailDiagonal_eq_sum`, `frobNorm_squareSVDTailDiagonal_eq_sqrt_sum` |
| RandNLA low-rank right-Gram singular values | Drineas-Mahoney, equation (9) | Exact analysis Gram `A^T A` is symmetric/PSD; its ordered Hermitian eigenvalues define nonnegative, antitone singular-value squares and square-root singular values; probabilities/laws remain exact | `rectRightGram`, `finiteQuadraticForm_rectRightGram_eq_sum_sq`, `rectRightGram_finitePSD`, `rectRightGram_matrix_posSemidef`, `rectSingularValueSq_nonneg`, `rectSingularValueSq_antitone`, `rectSingularValue_nonneg`, `rectSingularValue_antitone`, `rectSingularValue_sq_eq` |
| RandNLA low-rank right-Gram eigenvectors | Drineas-Mahoney, equation (9) | Exact mathlib eigenbasis of `A^T A` gives a basis-indexed orthogonal right singular-vector table, nonnegative basis-indexed singular values, and diagonalizes `V^T(A^T A)V`; probabilities/laws remain exact | `rectRightGramEigenbasis_isOrthogonal`, `rectRightGramEigenbasis_col_orthonormal`, `rectRightGramEigenbasis_row_orthonormal`, `rectRightGramEigenvalue_nonneg`, `rectRightGramBasisSingularValue_sq_eq`, `rectRightGramEigenbasis_eigenvector`, `rectRightGramEigenbasis_diagonalizes_singularValueSq` |
| RandNLA low-rank full-positive right-Gram reconstruction | Drineas-Mahoney, equation (9) | If every basis-indexed right-Gram singular value is positive, left candidates `u_a=A v_a/tau_a` are orthonormal and reconstruct `A=sum_a u_a tau_a v_a^T`; probabilities/laws remain exact | `rectRightGramProjectedColumn_dot_diagonal`, `rectRightGramLeftSingularFromEigenbasis_col_orthonormal_of_pos`, `rectRightGramProjectedColumn_reconstruct`, `rectRightGramLeftSingularFromEigenbasis_factor_column_of_pos`, `rectRightGram_fullPositive_basisSVD_representation` |
| RandNLA low-rank zero right-Gram projected columns | Drineas-Mahoney, equation (9) | The exact projected-column norm square satisfies `sum_i (A v_a)_i^2=tau_a^2=alpha_a`; if `tau_a=0` or `alpha_a=0`, then the projected column `A v_a` is coordinatewise zero; probabilities/laws remain exact | `rectRightGramProjectedColumn_normSq_eq_singularValue_sq`, `rectRightGramProjectedColumn_normSq_eq_eigenvalue`, `rectRightGramProjectedColumn_eq_zero_of_singularValue_eq_zero`, `rectRightGramProjectedColumn_eq_zero_of_eigenvalue_eq_zero` |
| RandNLA low-rank zero-safe right-Gram reconstruction | Drineas-Mahoney, equation (9) | Zero-safe left candidates use `0` when `tau_a=0` and `A v_a/tau_a` otherwise, giving `tau_a u_a=A v_a` and `A=sum_a u_a tau_a v_a^T` without a full-positive hypothesis; probabilities/laws remain exact | `rectRightGramLeftSingularZeroSafe`, `rectRightGramLeftSingularZeroSafe_factor_column`, `rectRightGram_basisSVD_representation` |
| RandNLA low-rank selected right-Gram head/tail split | Drineas-Mahoney, equation (9) | For any finite selected basis-index set `s`, the zero-safe reconstruction splits exactly as `A=Head_s+Tail_s`, and `Head_s` factors through `Fin s.card`; probabilities/laws remain exact | `rectRightGramBasisSVDHead`, `rectRightGramBasisSVDTail`, `rectRightGramBasisSVD_head_tail_entry`, `rectRightGramBasisSVDHeadRankFactorization`, `rectRightGramBasisSVDHead_rankAtMost` |
| RandNLA low-rank selected right-Gram sketch bridge | Drineas-Mahoney, equation (9) | The selected eigenvector sketch `Z_s` satisfies `A Z_s=A V_s`, and the selected head factors as `(A Z_s)V_s^T`; probabilities/laws remain exact | `rectRightGramBasisSketchMatrix`, `rectRightGramBasisSketchCoeff`, `columnSketch_rectRightGramBasisSketchMatrix`, `rectRightGramBasisSketch_head_eq`, `rectRightGramBasisSketchHeadFactorization`, `rectRightGramBasisSVDHead_columnSketchHeadFactorization` |
| RandNLA low-rank selected right-Gram equation-(9) certificate adapter | Drineas-Mahoney, equation (9) | The selected head/tail split and selected sketch bridge instantiate the equation-(9) rank/residual surface under explicit tail, coupling, projector-through-sketch, and reproduction hypotheses; probabilities/laws remain exact | `equation9HeadTailSketchCertificate_of_rectRightGramBasisSVDHead`, `equation9HeadTailSketchRankResidualSurface_of_rectRightGramBasisSVDHead` |
| RandNLA low-rank selected cardinality rank handoff | Drineas-Mahoney, equation (9) | A selected set with `s.card = k` transports the selected-head and equation-(9) rank certificates from `|s|` to displayed rank `k`; probabilities/laws remain exact | `rectRankAtMost_of_eq_rank`, `rectRightGramBasisSVDHead_rankAtMost_of_card_eq`, `equation9HeadTailSketchRankResidualSurface_of_rectRightGramBasisSVDHead_card_eq` |
| RandNLA low-rank selected-index embedding handoff | Drineas-Mahoney, equation (9) | An embedding `Fin k ↪ Fin n` induces a selected right-Gram index set of cardinality `k` and feeds the selected-head/equation-(9) rank-residual surfaces; probabilities/laws remain exact | `rectRightGramSelectedIndexSet`, `rectRightGramSelectedIndexSet_card`, `rectRightGramBasisSVDHead_rankAtMost_of_embedding`, `equation9HeadTailSketchRankResidualSurface_of_rectRightGramBasisSVDHead_embedding` |
| RandNLA low-rank semantic ordered-top embedding handoff | Drineas-Mahoney, equation (9) | A semantic certificate equating embedding-selected basis singular values with the first `k` ordered right-Gram singular values gives selected square/order facts and composes with the embedding rank/residual surface; probabilities/laws remain exact | `rectTopIndex`, `RectRightGramOrderedTopEmbeddingCertificate`, `rectRightGramOrderedTopEmbeddingCertificate_selected_sq_eq`, `rectRightGramOrderedTopEmbeddingCertificate_selected_antitone`, `equation9HeadTailSketchRankResidualSurface_of_rectRightGramBasisSVDHead_orderedTopEmbedding` |
| RandNLA low-rank constructed ordered-top embedding | Drineas-Mahoney, equation (9) | Mathlib's Hermitian spectral reindexing constructs the top-`k` embedding certificate for the exact right-Gram eigenbasis and specializes the ordered-top equation-(9) surface; probabilities/laws remain exact | `rectRightGramOrderedEigenbasisEquiv`, `rectRightGramOrderedTopEmbedding`, `rectRightGramOrderedTopEmbedding_certificate`, `equation9HeadTailSketchRankResidualSurface_of_rectRightGramBasisSVDHead_constructedOrderedTopEmbedding` |
| RandNLA low-rank ordered top/complement dominance | Drineas-Mahoney, equation (9) | The constructed top-`k` right-Gram embedding dominates every unselected basis-indexed singular direction; probabilities/laws remain exact | `rectRightGramBasisOrderedIndex`, `finCardIndex_rectRightGramBasisOrderedIndex`, `rectRightGramBasisSingularValue_eq_orderedIndex`, `rectRightGramOrderedTopEmbedding_not_mem_index_ge`, `rectTopIndex_le_rectRightGramBasisOrderedIndex_of_not_mem_orderedTopEmbedding`, `rectRightGramOrderedTopEmbedding_complement_singularValue_le_selected` |
| RandNLA low-rank top-k head positivity | Drineas-Mahoney, equation (9) | Positivity of the kth ordered right-Gram singular value gives positivity and nonzero selected head singular values for the constructed top-`k` embedding; probabilities/laws remain exact | `rectTopLastIndex`, `le_rectTopLastIndex`, `rectTopIndex_le_last`, `rectSingularValue_top_pos_of_last_pos`, `rectRightGramOrderedTopEmbedding_selected_pos_of_last_pos`, `rectRightGramOrderedTopEmbedding_selected_nonzero_of_last_pos` |
| RandNLA low-rank top-k left-basis orthonormality | Drineas-Mahoney, equation (9) | Positive selected singular values make the zero-safe left singular-vector candidates orthonormal on the constructed top-`k` block; probabilities/laws remain exact | `rectRightGramLeftSingularZeroSafe_col_orthonormal_of_pos`, `rectRightGramOrderedTopEmbedding_leftZeroSafe_col_orthonormal_of_last_pos` |
| RandNLA low-rank ordered source-head factorization | Drineas-Mahoney, equation (9) | The constructed top-`k` selected right-Gram head equals `U_ord Sigma_ord V_ord^T`, with exact left/right column orthonormality under the kth-singular-value positivity hypothesis; probabilities/laws remain exact | `rectRightGramOrderedHeadLeft`, `rectRightGramOrderedHeadRight`, `rectRightGramOrderedHeadSingularDiagonal`, `sourceSVDFactorMatrix_rectRightGramOrderedHead_entry`, `rectRightGramBasisSVDHead_orderedTopEmbedding_eq_sourceSVDFactorMatrix`, `rectRightGramOrderedHeadLeft_col_orthonormal_of_last_pos`, `rectRightGramOrderedHeadRight_col_orthonormal` |
| RandNLA low-rank ordered source-tail factorization | Drineas-Mahoney, equation (9) | The constructed top-`k` complement tail equals `U_tail Sigma_tail V_tail^T`, the tail right factor has exact orthonormal columns, and the ordered source head plus this source tail reconstructs `A`; probabilities/laws remain exact | `rectRightGramBasisSVDTailLeft`, `rectRightGramBasisSVDTailRight`, `rectRightGramBasisSVDTailSingularDiagonal`, `rectRightGramOrderedTailLeft`, `rectRightGramOrderedTailRight`, `rectRightGramOrderedTailSingularDiagonal`, `rectRightGramBasisSVDTailRight_col_orthonormal`, `rectRightGramOrderedTailRight_col_orthonormal`, `sourceSVDFactorMatrix_rectRightGramBasisSVDTail_entry`, `rectRightGramBasisSVDTail_eq_sourceSVDFactorMatrix`, `rectRightGramBasisSVDTail_orderedTopEmbedding_eq_sourceSVDFactorMatrix`, `rectRightGramOrdered_source_head_add_tail` |
| RandNLA low-rank ordered right-basis block completeness | Drineas-Mahoney, equation (9) | The constructed complement-tail and top-`k` head right tables form an exact column-orthonormal and row-complete right-basis block; probabilities/laws remain exact | `rectRightGramSelectedIndexSet_sum`, `rectRightGramComplement_sum_orderEmbOfFin`, `rectRightGramSelectedIndexSet_head_tail_cross_zero`, `rectRightGramSelectedIndexSet_tail_head_cross_zero`, `rectRightGramSelectedIndexSet_tail_head_row_complete`, `rectRightGramOrderedRightBasisBlock_col_orthonormal`, `rectRightGramOrderedRightBasisBlock_row_orthonormal`, `rectRightGramOrderedRightBasisBlock_col_row_orthonormal` |
| RandNLA low-rank constructed ordered block certificate | Drineas-Mahoney, equation (9) | The constructed ordered source split and right-basis block instantiate `BlockDiagonalSourceSVDTailCertificate` once left-block columns and head nonzero/positivity fields are supplied; probabilities/laws remain exact | `leftBasisBlock_col_orthonormal_of_component_orthonormal_fields`, `BlockDiagonalSourceSVDTailCertificate.of_rectRightGramOrderedSourceSplit`, `BlockDiagonalSourceSVDTailCertificate.of_rectRightGramOrderedSourceSplit_component_left`, `BlockDiagonalSourceSVDTailCertificate.of_rectRightGramOrderedSourceSplit_component_left_of_last_pos` |
| RandNLA low-rank ordered head-tail left cross field | Drineas-Mahoney, equation (9) | Kth ordered singular-value positivity makes the constructed ordered head-left block orthogonal to the complement tail-left zero-safe block, so the ordered block certificate only needs tail-left orthonormality; probabilities/laws remain exact | `rectRightGramLeftSingularZeroSafe_cross_zero_of_pos_ne`, `rectRightGramOrderedHeadTailLeft_cross_zero_of_last_pos`, `BlockDiagonalSourceSVDTailCertificate.of_rectRightGramOrderedSourceSplit_tail_left_of_last_pos` |
| RandNLA low-rank positive-complement tail-left field | Drineas-Mahoney, equation (9) | If every complement-enumerated singular value is strictly positive, the constructed complement tail-left zero-safe table has exact orthonormal columns and closes the ordered block certificate under kth head positivity; probabilities/laws remain exact | `rectRightGramBasisSVDTailLeft_col_orthonormal_of_pos`, `rectRightGramOrderedTailLeft_col_orthonormal_of_complement_pos`, `BlockDiagonalSourceSVDTailCertificate.of_rectRightGramOrderedSourceSplit_all_tail_pos_of_last_pos` |
| RandNLA low-rank zero-tail obstruction | Drineas-Mahoney, equation (9) | If a complement singular value is zero, the corresponding zero-safe tail-left column has self-dot zero, so the raw zero-safe tail table cannot be the orthonormal tail basis for the block certificate; probabilities/laws remain exact | `rectRightGramBasisSVDTailLeft_self_dot_eq_zero_of_singularValue_eq_zero`, `not_rectRightGramBasisSVDTailLeft_col_orthonormal_of_zero_singularValue`, `not_rectRightGramOrderedTailLeft_col_orthonormal_of_zero_complement_singularValue`, `not_BlockDiagonalSourceSVDTailCertificate_rectRightGramOrdered_zero_safe_tail_of_zero_complement_singularValue` |
| RandNLA low-rank replacement tail-left adapter | Drineas-Mahoney, equation (9) | A nullspace-completed replacement tail-left table preserves the exact source-tail factor if it agrees with the zero-safe table on nonzero complement singular directions, and it feeds the ordered block certificate when it is orthonormal and head-orthogonal; probabilities/laws remain exact | `sourceSVDFactorMatrix_rectRightGramBasisSVDTail_replacement_left_entry`, `rectRightGramBasisSVDTail_eq_sourceSVDFactorMatrix_replacement_left`, `rectRightGramOrdered_source_head_add_tail_replacement_left`, `BlockDiagonalSourceSVDTailCertificate.of_rectRightGramOrderedSourceSplit_replacement_tail_left_of_last_pos` |
| RandNLA low-rank left-block dimension guard | Drineas-Mahoney, equation (9) | Any exact column-orthonormal left block `[U,Utail]` with `r+q` columns in `R^m` forces `r+q <= m`, so the nullspace-completed route must expose the tall/thin dimension condition or change the rectangular SVD surface; probabilities/laws remain exact | `colOrthonormal_fintype_card_le_rows`, `leftBasisBlock_col_orthonormal_card_le_rows`, `BlockDiagonalSourceSVDTailCertificate.left_column_count_le_row_dim` |
| RandNLA low-rank partial left-block completion | Drineas-Mahoney, equation (9) | Any exact partially specified orthonormal column family in `R^m` can be completed to a full `m x m` orthonormal table; embedded block columns give a replacement tail-left table preserving specified tail columns and making `[U,Utail]` orthonormal; probabilities/laws remain exact | `partialColOrthonormal_exists_fullColOrthonormal`, `partialLeftBasisBlock_exists_replacement_tail` |
| RandNLA low-rank ordered nonzero-tail completion | Drineas-Mahoney, equation (9) | The constructed ordered top-`k` split now instantiates the partial set containing all head columns and exactly the nonzero complement-tail directions; a supplied embedding into `Fin m` yields a replacement tail-left table agreeing on nonzero tail directions and a full ordered block source-SVD certificate; probabilities/laws remain exact | `rectRightGramOrderedNonzeroTailPartialSet_leftBasisBlock_col_orthonormal_of_last_pos`, `exists_rectRightGramOrdered_replacement_tail_left_block_certificate_of_last_pos` |
| RandNLA low-rank ordered replacement-tail rank surface | Drineas-Mahoney, equation (9) | The nullspace-completed ordered source split feeds the exact block-certificate equation-(9) rank/residual surface under visible `det(V_ord^T Z) != 0` and cross-term hypotheses; probabilities/laws remain exact | `exists_columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_rectRightGramOrdered_replacement_tail_left_of_last_pos` |
| RandNLA low-rank ordered replacement-tail relative surface | Drineas-Mahoney, equation (9) | The same ordered source split feeds the exact block-certificate relative surface when tail optimality and scalar comparison are supplied explicitly; probabilities/laws remain exact | `exists_columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectRightGramOrdered_replacement_tail_left_of_last_pos` |
| RandNLA low-rank ordered tail-diagonal norm | Drineas-Mahoney, equation (9) | The constructed ordered complement-tail singular diagonal has squared Frobenius norm equal to the sum of the complement singular-value squares; probabilities/laws remain exact | `frobNormSq_diagonal_eq_sum`, `frobNorm_diagonal_eq_sqrt_sum`, `frobNormSq_rectRightGramOrderedTailSingularDiagonal_eq_sum`, `frobNorm_rectRightGramOrderedTailSingularDiagonal_eq_sqrt_sum` |
| RandNLA low-rank exact column-permutation transport | Drineas-Mahoney, equation (9) | Exact column reindexing preserves explicit rank factorizations, rank-at-most certificates, and Frobenius residuals when source and competitor are reindexed together; probabilities/laws remain exact | `RectRankFactorization.permuteCols`, `RectRankAtMost.permuteCols`, `RectRankAtMost.of_permuteCols`, `lowRankResidualFrob_permuteCols` |
| RandNLA low-rank ordered head-tail column equivalence | Drineas-Mahoney, equation (9) | The constructed ordered top-k embedding plus complement-tail enumeration is a bijective exact column map and induces the explicit `Fin (k+q) ≃ Fin n` transport; probabilities/laws remain exact | `rectRightGramOrderedHeadTailColumnMap`, `rectRightGramOrderedHeadTailColumnMap_injective`, `rectRightGramOrderedHeadTailColumnMap_surjective`, `rectRightGramOrderedHeadTailColumnSumEquiv`, `rectRightGramOrderedHeadTailColumnEquiv` |
| RandNLA low-rank cross-domain column-equivalence transport | Drineas-Mahoney, equation (9) | Exact column reindexing along `Fin p ≃ Fin n` preserves rank-at-most certificates and Frobenius residuals, with ordered head-tail wrappers for LR.1dz; probabilities/laws remain exact | `rectReindexCols`, `RectRankFactorization.reindexCols`, `RectRankAtMost.reindexCols`, `RectRankAtMost.of_reindexCols`, `lowRankResidualFrob_reindexCols`, `lowRankResidualFrob_rectRightGramOrderedHeadTailColumnEquiv` |
| RandNLA low-rank constructed tail-optimality discharge | Drineas-Mahoney, equation (9) | The ordered replacement-tail split now proves the Frobenius tail-optimality inequality for every exact rank-at-most-k competitor and feeds the relative surface without a supplied `hopt`; probabilities/laws remain exact | `frobNorm_rectRightGramOrderedTailSingularDiagonal_le_lowRankResidualFrob`, `exists_columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectRightGramOrdered_replacement_tail_left_of_last_pos_tailOptimal` |
| RandNLA low-rank scalar-relative tail-optimal surface | Drineas-Mahoney, equation (9) | The ordered replacement-tail relative surface now accepts the coefficient comparison `2*sqrt(1+eps^2) <= rho`; the product-form comparison follows by multiplying by the nonnegative exact tail norm; probabilities/laws remain exact | `two_sqrt_one_add_sq_mul_tail_le_of_scalar`, `exists_columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectRightGramOrdered_replacement_tail_left_of_last_pos_tailOptimal_of_scalarRelative` |
| RandNLA low-rank stored projector application FP certificate | Drineas-Mahoney, equation (9) | Concrete implementation-facing certificate for storing the exact Gram-inverse projector by rounded multiply-one copies and then applying it to `A` with a rounded length-`m` product; Gram construction and inversion routines remain ledger obligations; probabilities/laws remain exact | `columnSketchGramInverseProjectorStoredMulOne`, `fl_columnSketchGramInverseProjectorStoredMulOne_preconditionRows_entry_error_bound` |
| RandNLA low-rank ordered head-tail cardinality bridge | Drineas-Mahoney, equation (9) | The constructed ordered top set and complement-tail index type satisfy `k + q = n`, giving the Fin/cardinality bridge needed before reindexing into q-dimensional Eckart-Young transport; probabilities/laws remain exact | `rectRightGramSelectedIndexSet_card_add_compl_card`, `rectRightGramOrderedTailIndex_card_add` |
| RandNLA low-rank constructed ordered head-tail square gap | Drineas-Mahoney, equation (9) | The last selected top singular square separates every selected head square from every complement-tail square, supplying the exact LR.1dw gap shape for unsorted complement-tail enumerations; probabilities/laws remain exact | `rectRightGramOrdered_head_tail_square_gap` |
| RandNLA low-rank source-tail norm reduction | Drineas-Mahoney, equation (9) | `frobNormSqRect_leftOrthonormalFactor`, `frobNormRect_leftOrthonormalFactor`, `sourceSketchResidualTail_leftFactor` | `frobNormSqRect_sourceSketchResidualTail_leftOrthonormalFactor`, `frobNormRect_sourceSketchResidualTail_leftOrthonormalFactor` |
| RandNLA low-rank coordinate-tail residual factorization | Drineas-Mahoney, equation (9) | `sourceRightBasisTranspose`, `rightSketchCrossGramRect`, `sourceSketchResidualTail_leftSquareFactor` | `sourceSketchResidualTail_sigmaRightBasisTranspose_explicit`, `frobNormRect_sourceSketchResidualTail_sigmaRightBasisTranspose_le` |
| RandNLA low-rank right-tail residual block products | Drineas-Mahoney, equation (9) | `rightSketchCrossGramRectInvFactor`, `sourceSketchCoefficient_mul_rightTailBasis_of_cross_zero`, `sourceSketchCoefficient_mul_headRightBasis_of_orthonormal` | `sourceRightResidual_mul_rightTailBasis_eq_id`, `sourceRightResidual_mul_headRightBasis_eq_neg_invFactor` |
| RandNLA low-rank right-tail Frobenius block identity | Drineas-Mahoney, equation (9) | `finiteFrobNormSq_rectRightOrthonormal`, `rightBasisBlock`, `sourceRightResidualBlock`, `sigmaRightResidualBlock` | `sourceRightResidual_sigma_rightBasisBlock_eq_block`, `frobNormSqRect_sigma_sourceRightResidual_eq_block`, `frobNormRect_sigma_sourceRightResidual_eq_sqrt_block` |
| RandNLA low-rank right-basis block orthonormality certificate | Drineas-Mahoney, equation (9) | Exact column and row orthonormality of the concatenated block `[V_perp,V_k]` | `rightBasisBlock_component_orthonormal_fields_of_col_orthonormal`, `rightBasisBlock_complete_sum_of_row_orthonormal`, `frobNormRect_sigma_sourceRightResidual_le_sqrt_one_add_eps_sq_of_rightBasisBlock_orthonormal` |
| RandNLA low-rank right-basis block assembly | Drineas-Mahoney, equation (9) | Separate exact component fields `V_perp^T V_perp=I`, `V_k^T V_perp=0`, `V_perp^T V_k=0`, `V_k^T V_k=I`, plus row completeness | `rightBasisBlock_col_orthonormal_of_component_orthonormal_fields`, `rightBasisBlock_col_row_orthonormal_of_component_fields`, `frobNormRect_sigma_sourceRightResidual_le_sqrt_one_add_eps_sq_of_component_block_assembly` |
| RandNLA low-rank source cross-term certificate | Drineas-Mahoney, equation (9) | `frobNormRect_sigma_sourceRightResidual_eq_sqrt_block` | `frobNormRect_sigma_sourceRightResidual_le_sqrt_one_add_eps_sq` |
| RandNLA low-rank ambient source-tail certificate | Drineas-Mahoney, equation (9) | `frobNormRect_sourceSketchResidualTail_leftOrthonormalFactor`, `sourceSketchResidualTail_leftSquareFactor`, `frobNormRect_sigma_sourceRightResidual_le_sqrt_one_add_eps_sq` | `frobNormRect_sourceSketchResidualTail_sourceSVDTail_le_sqrt_one_add_eps_sq` |
| RandNLA low-rank projected source-tail coupling certificate | Drineas-Mahoney, equation (9) | `finiteVecNorm2_finiteMatVec_le_of_symmetric_idempotent`, `frobNormRect_preconditionRows_le_of_symmetric_idempotent`, `ColumnSketchOrthogonalProjectorCertificate`, `ColumnSketchMoorePenroseCertificate` | `frobNormRect_preconditionRows_columnSketchLeftMultiplier_le_of_orthogonalProjectorCertificate`, `frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_orthogonalProjector_le_sqrt_one_add_eps_sq`, `frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_sq` |
| RandNLA low-rank transpose-action spectral coupling certificate | Drineas-Mahoney, equation (9) | `rectOpNorm2Le`, `finiteTranspose`, `frobNormRect_matMulRectLeft_le_of_transpose_rectOpNorm2Le` | `frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_transpose_rectOpNorm2Le`, `frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_sq_of_transpose_rectOpNorm2Le` |
| RandNLA low-rank ordinary operator coupling certificate | Drineas-Mahoney, equation (9) | `rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le`, `frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_rectOpNorm2Le` | `frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_sq_of_rectOpNorm2Le` |
| RandNLA low-rank computed cross-factor perturbation certificate | Drineas-Mahoney, equation (9) | `rectOpNorm2Le`, `frobNormRect`, exact probabilities/laws | `frobNormRect_sigma_exactFactor_le_of_computed_rectOpNorm2Le_of_frobNormRect_error`, `frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_computed_rectOpNorm2Le_of_frobNormRect_error`, `frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_plus_tau_sq_of_computed_rectOpNorm2Le` |
| RandNLA low-rank entrywise computed cross-factor certificate | Drineas-Mahoney, equation (9) | `frobNormRect_le_sqrt_mul_nat_of_entry_abs_le`, entrywise non-probability error budget | `frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_computed_rectOpNorm2Le_of_entry_abs_error`, `frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_plus_entry_sq_of_computed_rectOpNorm2Le` |
| RandNLA low-rank component-certified computed cross-factor certificate | Drineas-Mahoney, equation (9) | `rectMatMul_entry_abs_sub_computed_le_of_component_sums`, cross-gram/inverse/product component budgets | `rightSketchCrossGramRectInvFactor_entry_abs_error_le_of_component_sums`, `frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_computed_rectOpNorm2Le_of_component_error`, `frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_plus_component_sq_of_computed_rectOpNorm2Le` |
| RandNLA low-rank fl-matmul cross-gram component certificate | Drineas-Mahoney, equation (9) | `flRightSketchCrossGramRect`, `rightSketchCrossGramRectDotBudget`, concrete `fl_matMul((Vperp^T)Z)` dot-product budget | `rightSketchCrossGramRect_flMatMul_entry_abs_error_le`, `rightSketchCrossGramRectInvFactor_entry_abs_error_le_of_flMatMul_crossGram_component_sums`, `frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_plus_flMatMul_crossGram_component_sq_of_computed_rectOpNorm2Le` |
| RandNLA low-rank fl-matmul square cross-Gram inverse-input certificate | Drineas-Mahoney, equation (9) | `flRightSketchCrossGram`, `rightSketchCrossGramDotBudget`, concrete `fl_matMul((V_k^T)Z)` dot-product budget | `rightSketchCrossGram_flMatMul_entry_abs_error_le`, `frobNorm_rightSketchCrossGram_sub_flMatMul_le_of_dotBudget_le` |
| RandNLA low-rank inverse-entry computed-factor adapter | Drineas-Mahoney, equation (9) | Entrywise inverse error `eta`, computed left-factor row-sum budget `chi` | `rightSketchCrossGramRectInvFactor_inverse_component_sum_le_of_entry_abs_error`, `rightSketchCrossGramRectInvFactor_entry_abs_error_le_of_flMatMul_crossGram_inverse_entry_abs_error`, `frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_plus_flMatMul_crossGram_inverse_entry_sq_of_computed_rectOpNorm2Le` |
| RandNLA low-rank fl-matmul final cross-factor product | Drineas-Mahoney, equation (9) | `flRightSketchCrossGramRectInvFactorProduct`, product dot-budget `gamma(fp,r) sum |Xhat||Yhat|` | `rightSketchCrossGramRectInvFactorProduct_flMatMul_entry_abs_error_le`, `rightSketchCrossGramRectInvFactor_entry_abs_error_le_of_flMatMul_crossGram_inverse_entry_abs_error_flMatMul_product`, `frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_plus_flMatMul_crossGram_inverse_entry_flMatMul_product_sq_of_computed_rectOpNorm2Le` |
| RandNLA low-rank product Frobenius-to-operator handoff | Drineas-Mahoney, equation (9) | Visible `frobNormRect Mhat <= eps` certificate for `Mhat = fl(fl((Vperp^T)Z) Yhat)` | `rectOpNorm2Le_flRightSketchCrossGramRectInvFactorProduct_of_frobNormRect_le`, `frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_frobNormRect_flMatMul_crossGram_inverse_entry_flMatMul_product`, `frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_frobNormRect_flMatMul_crossGram_inverse_entry_flMatMul_product_sq` |
| RandNLA low-rank product absolute-sum Frobenius certificate | Drineas-Mahoney, equation (9) | Product magnitude budget `sum |Xhat||Yhat| <= kappa` plus final product rounding budget `rho` | `rightSketchCrossGramRectInvFactorProduct_entry_abs_le_of_product_sum_budget`, `frobNormRect_flRightSketchCrossGramRectInvFactorProduct_le_sqrt_mul_product_sum_budget`, `rectOpNorm2Le_flRightSketchCrossGramRectInvFactorProduct_of_product_sum_budget`, `frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_product_sum_budget_flMatMul_crossGram_inverse_entry_flMatMul_product_sq` |
| RandNLA low-rank perturbed-inverse eta certificate | Drineas-Mahoney, equation (9); Higham §14.1 | Perturbed inverse equation `(A+DeltaA) Yhat = I`, componentwise `DeltaA` budget, and inverse sensitivity budget | `nonsingInv_entry_abs_sub_computed_inverse_le_of_perturbed_inverse_component_budget`, `rightSketchCrossGram_inverse_entry_abs_error_le_of_perturbed_inverse_component_budget`, `frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_perturbed_inverse_product_sum_budget_sq` |
| RandNLA low-rank Method-A LU inverse eta certificate | Drineas-Mahoney, equation (9); Higham §14.3 Method A | `methodAComputedInverse` from LU solves, `LUBackwardError`, and visible Method-A forward-error budget | `methodA_computed_inverse_entry_abs_sub_nonsingInv_le_of_lu_budget`, `rightSketchCrossGram_inverse_entry_abs_error_le_of_methodA_lu_budget`, `frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_methodA_inverse_product_sum_budget_sq` |
| RandNLA low-rank Method-A computed-input LU certificate | Drineas-Mahoney, equation (9); Higham §§9.3--9.4, 14.3 | LU factors certified for a rounded square cross Gram, input-transfer coefficient `mu`, and Method-A budget with `(epsLU+mu)+2*gamma+gamma^2` | `rightSketchCrossGram_LUBackwardError_of_flRightSketchCrossGram_input_budget`, `rightSketchCrossGram_inverse_entry_abs_error_le_of_methodA_fl_lu_input_budget`, `frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_methodA_lu_factor_product_sum_budget_sq` |
| RandNLA low-rank Doolittle Method-A computed-input LU certificate | Drineas-Mahoney, equation (9); Higham §§9.2--9.4, 14.3 | `DoolittleLU` recurrence certificate for `flRightSketchCrossGram`, input-transfer coefficient `mu`, and Method-A budget with `(gamma+mu)+2*gamma+gamma^2` | `DoolittleLU.to_LUBackwardError`, `rightSketchCrossGram_LUBackwardError_of_DoolittleLU_flRightSketchCrossGram`, `rightSketchCrossGram_inverse_entry_abs_error_le_of_methodA_doolittle_fl_input_budget`, `frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_methodA_doolittle_fl_input_product_sum_budget_sq` |
| RandNLA low-rank dense-loop Doolittle Method-A certificate | Drineas-Mahoney, equation (9); Higham §§9.2--9.4, 14.3 | Literal `flDoolittleUEntry`/`flDoolittleLEntry` fold equalities plus visible residual-compression budgets feeding `DoolittleLU` | `DoolittleDenseLoopCertificate.to_DoolittleLU`, `DoolittleDenseLoopCertificate.to_LUBackwardError`, `rightSketchCrossGram_LUBackwardError_of_DoolittleDenseLoopCertificate_flRightSketchCrossGram`, `frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_methodA_doolittleDenseLoop_fl_input_product_sum_budget_sq` |
| RandNLA low-rank dense-loop Doolittle absolute-budget certificate | Drineas-Mahoney, equation (9); Higham §§9.2--9.4, 14.3 | Absolute residual budgets `BU`/`BL` for literal Doolittle folds plus dominance inequalities turning them into residual-compression budgets | `DoolittleDenseLoopAbsBudgetCertificate.to_denseLoopCertificate`, `DoolittleDenseLoopAbsBudgetCertificate.to_LUBackwardError`, `rightSketchCrossGram_LUBackwardError_of_DoolittleDenseLoopAbsBudgetCertificate_flRightSketchCrossGram`, `frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_methodA_doolittleDenseLoopAbsBudget_fl_input_product_sum_budget_sq` |
| RandNLA low-rank Doolittle rounded-product fold budgets | Drineas-Mahoney, equation (9); Higham §§3.1, 9.2 | Generic subtraction-fold absolute residual bound specialized to Doolittle upper and lower-numerator folds against the rounded products actually subtracted | `fl_sub_sum_error_init_abs_residual_le`, `flDoolittleUEntry_rounded_residual_abs_le`, `flDoolittleLNumerator_rounded_residual_abs_le` |
| RandNLA low-rank Doolittle exact-product fold budgets | Drineas-Mahoney, equation (9); Higham §§2.2, 3.1, 9.2 | Product-roundoff transfer from rounded products back to exact `Lhat*Uhat` products in the upper and lower-numerator Doolittle folds | `fl_mul_abs_sub_mul_le`, `flDoolittleUEntry_exact_product_residual_abs_le`, `flDoolittleLNumerator_exact_product_residual_abs_le` |
| RandNLA low-rank Doolittle masked-prefix fold budgets | Drineas-Mahoney, equation (9); Higham §§2.2, 3.1, 9.2 | Reindex exact-product Doolittle fold residuals from `Fin k` sums into the masked `Fin n` recurrence-certificate shape | `finMaskedPrefixSum_eq_finSum`, `flDoolittleUEntry_masked_exact_product_residual_abs_le`, `flDoolittleLNumerator_masked_exact_product_residual_abs_le` |
| RandNLA low-rank Doolittle lower division/pivot budgets | Drineas-Mahoney, equation (9); Higham §§2.2, 9.2 | Charge the rounded lower-entry division and multiplication by the computed pivot, then combine it with the masked exact-product lower-numerator budget | `flDoolittleLEntry_mul_pivot_sub_numerator_abs_le`, `flDoolittleLEntry_masked_exact_product_residual_abs_le` |
| RandNLA low-rank Doolittle literal source-budget certificate | Drineas-Mahoney, equation (9); Higham §§2.2, 3.1, 9.2 | Concrete `BU`/`BL` formulas from literal Doolittle arithmetic plus visible dominance inequalities instantiate `DoolittleDenseLoopAbsBudgetCertificate` | `doolittleUAbsBudget`, `doolittleLAbsBudget`, `DoolittleDenseLoopAbsBudgetCertificate.of_literal_doolittle_source_budgets` |
| RandNLA low-rank Doolittle component dominance certificate | Drineas-Mahoney, equation (9); Higham §§2.2, 3.1, 9.2 | Componentwise no-cancellation bounds for upper work/products and lower work/products/numerator imply the concrete `BU`/`BL` dominance inequalities | `doolittleUAbsBudget_le_compression_of_component_dominance`, `doolittleLAbsBudget_le_compression_of_component_dominance`, `DoolittleDenseLoopAbsBudgetCertificate.of_literal_doolittle_component_dominance` |
| RandNLA low-rank Doolittle exact-product margin certificate | Drineas-Mahoney, equation (9); Higham §§2.2, 3.1, 9.2 | Exact-product no-cancellation margins with the explicit `(1+u_fp)` rounded-product growth factor imply the dense-loop component dominance certificate | `fl_mul_abs_le_one_add_u_mul_abs_mul`, `doolittleUWorkAbs_le_of_exact_product_margin`, `doolittleLWorkAbs_le_of_exact_product_margin`, `DoolittleDenseLoopAbsBudgetCertificate.of_literal_doolittle_exact_product_margins` |
| RandNLA low-rank Doolittle numerator-margin certificate | Drineas-Mahoney, equation (9); Higham §§2.2, 3.1, 9.2 | A stronger exact-product lower-numerator margin dominates the rounded lower numerator and removes the remaining separate numerator-dominance assumption | `doolittleLNumeratorAbs_le_of_exact_product_numerator_margin`, `DoolittleDenseLoopAbsBudgetCertificate.of_literal_doolittle_exact_product_numerator_margins` |
| RandNLA low-rank Doolittle exact-target gap certificate | Drineas-Mahoney, equation (9); Higham §§2.2, 3.1, 9.2 | Exact pre-rounded Doolittle target gaps plus literal rounded-fold and pivot residual budgets imply the exact-product and numerator margins for the dense-loop certificate | `doolittleUExactTarget`, `doolittleLExactTarget`, `doolittleUExactProductMargin_of_exactTarget_gap`, `doolittleLExactProductMargin_of_exactTarget_gap`, `doolittleLExactProductNumeratorMargin_of_exactTarget_gap`, `DoolittleDenseLoopAbsBudgetCertificate.of_literal_doolittle_exact_target_gaps` |
| RandNLA low-rank Doolittle exact-target gap audit | Drineas-Mahoney, equation (9); Higham §§2.2, 3.1, 9.2 | Triangle bounds show the LR.1bp exact-target source gaps force their FP excess terms to be nonpositive, ruling out that source route whenever the excess is positive | `doolittleUExactTarget_abs_le_source_plus_productAbs`, `doolittleLExactTarget_abs_le_source_plus_productAbs`, `doolittleUExactTarget_gap_excess_nonpos`, `doolittleLExactTarget_gap_excess_nonpos`, `doolittleLExactTarget_numerator_gap_excess_nonpos` |
| Recursive summation | Higham §4.1–4.2, §4.6 | `fl_recursiveSum`, `recursiveSum_backward_error`, `recursiveSum_forward_error_bound`, `recursiveSum_forward_error_bound_oneSigned`, `recursiveSum_relError_le_gamma_of_oneSigned`, `recursiveSum_running_error_bound`, `HigherPrecisionRecursiveSumTrace`, `fl_higherPrecisionRecursiveSum` |
| Insertion summation examples | Higham §4.1–4.2 | `IncreasingAbsList`, `IncreasingAbsList.head_le_of_mem_of_nonnegative`, `insertion_first_two_exact_sum_le_head_tail_sum_of_nonnegative`, `insertion_first_two_exact_sum_le_tail_pair_sum_of_nonnegative`, `insertion_first_two_exact_sum_le_pair_sum_of_nonnegative`, `insertIncreasingAbs`, `insertIncreasingAbs_ne_nil`, `insertionStep`, `insertionStep_ne_nil_of_ne_nil`, `insertionActiveAfter`, `insertionActiveAfter_preserves_increasingAbs`, `insertionActiveAfter_ne_nil_of_ne_nil`, `insertionActiveAfter_full_length_le_one`, `insertionActiveAfter_full_length_eq_one_of_ne_nil`, `insertionActiveAfter_full_eq_singleton_of_ne_nil`, `fl_insertionSumList`, `fl_insertionSumList_eq_of_activeAfter_eq_singleton`, `fl_insertionSumList_eq_terminal_singleton_of_ne_nil`, `InsertionScheduleTree`, `InsertionScheduleTree.leafCount`, `InsertionScheduleTree.leaves_length`, `InsertionScheduleTree.toSumTree`, `InsertionScheduleTree.leafVector`, `InsertionScheduleTree.leafVector_eq_leaves_get`, `InsertionScheduleTree.toSumTree_eval`, `InsertionScheduleTree.exactEval`, `InsertionScheduleTree.exactEval_eq_leaves_sum`, `InsertionScheduleTree.exactEval_eq_of_leaves_perm`, `InsertionScheduleTree.exactMergeCost`, `InsertionScheduleTree.weightedLeafDepthCost`, `InsertionScheduleTree.leafDepthWeights`, `InsertionScheduleTree.weightedDepthPairsCost`, `InsertionScheduleTree.exactMergeCost_nonneg`, `InsertionScheduleTree.leafDepthWeights_weights_eq_leaves`, `InsertionScheduleTree.weightedLeafDepthCost_eq_weightedDepthPairsCost`, `InsertionScheduleTree.weightedLeafDepthCost_succ_eq_add_exactEval`, `InsertionScheduleTree.weightedLeafDepthCost_nonneg_of_leaves_nonnegative`, `InsertionScheduleTree.weightedLeafDepthCost_mono_startDepth_of_leaves_nonnegative`, `InsertionScheduleTree.weightedLeafDepthCost_leaf_pair_exchange_le`, `InsertionScheduleTree.weightedDepthPairsCost_pair_exchange_le`, `InsertionScheduleTree.exactEval_nonneg_of_leaves_nonnegative`, `InsertionScheduleTree.exactMergeCost_node_of_nonnegative`, `InsertionScheduleTree.exactMergeCost_eq_weightedLeafDepthCost_of_leaves_nonnegative`, `InsertionScheduleTree.eval_exactWithUnitRoundoff`, `InsertionScheduleTree.toSumTree_eval_exactWithUnitRoundoff`, `InsertionScheduleTree.toSumTree_runningErrorBudget_exactWithUnitRoundoff`, `fl_insertionSumList_has_list_schedule_of_ne_nil`, `fl_insertionSumList_has_sumTree_shape_of_ne_nil`, `fl_insertionSumList_has_sumTree_eval_of_ne_nil`, `insertionPowersFourTree`, `insertionPowersFour_exact_order`, `fl_insertionPowersFour_eq`, `fl_insertionPowersFour_eq_recursiveSum`, `insertionPowersFour_backward_error`, `insertionPowersFour_forward_error_bound`, `insertionPowersFour_running_error_bound_from_inverse_models`, `insertionPowersFour_relError_le_gamma_of_oneSigned`, `insertionNearOneFourTree`, `insertionNearOneFour_exact_order`, `fl_insertionNearOneFour_eq`, `fl_insertionNearOneFour_eq_pairwiseSum`, `insertionNearOneFour_backward_error`, `insertionNearOneFour_forward_error_bound`, `insertionNearOneFour_running_error_bound_from_inverse_models`, `insertionNearOneFour_relError_le_gamma_of_oneSigned` |
| Insertion separated weighted-depth exchange | Higham §4.2, p. 91 | `InsertionScheduleTree.weightedDepthPairsCost_pair_exchange_separated_le`, `InsertionScheduleTree.weightedDepthPairsCost_pair_exchange_separated_of_perm_le_and_weights_perm`, `InsertionScheduleTree.weightedDepthPairsCost_pair_exchange_of_context_min_le_and_weights_perm`, `InsertionScheduleTree.weightedDepthPairsCost_pair_exchange_of_left_deepest_two_smallest_decomposition_le_and_weights_perm`, `InsertionScheduleTree.weightedDepthPairsCost_pair_exchange_of_right_deepest_two_smallest_decomposition_le_and_weights_perm`, `InsertionScheduleTree.weightedDepthPairsCost_pair_exchange_of_left_deepest_second_two_smallest_decomposition_le_and_weights_perm`, `InsertionScheduleTree.weightedDepthPairsCost_pair_exchange_of_right_deepest_second_two_smallest_decomposition_le_and_weights_perm` |
| Insertion two-slot weighted-depth exchange | Higham §4.2, p. 91 | `InsertionScheduleTree.weightedDepthPairsCost_two_pair_exchange_separated_le`, `InsertionScheduleTree.weightedDepthPairsCost_two_pair_exchange_separated_of_perm_le`, `InsertionScheduleTree.weightedDepthPairsCost_two_pair_exchange_of_context_min_le`, `InsertionScheduleTree.weightedDepthPairsCost_two_pair_exchange_of_context_min_le_and_weights_perm`, `InsertionScheduleTree.weightedDepthPairsCost_two_pair_exchange_of_two_smallest_decomposition_le_and_weights_perm`, `InsertionScheduleTree.TwoSmallestDeepestExchangeBranch`, `InsertionScheduleTree.weightedDepthPairsCost_two_smallest_deepest_exchange_branch_le_and_weights_perm`, `InsertionScheduleTree.weightedLeafDepthCost_two_smallest_deepest_exchange_branch_realized_le_and_leaves_perm` |
| Insertion sibling weighted-depth contraction | Higham §4.2, p. 91 | `InsertionScheduleTree.weightedLeafDepthCost_node_eq_children_at_depth_add_exactEval`, `InsertionScheduleTree.weightedLeafDepthCost_node_leaf_leaf_eq_contract`, `InsertionScheduleTree.weightedDepthPairsCost_pair_contract_eq` |
| Insertion deepest sibling pair | Higham §4.2, p. 91 | `InsertionScheduleTree.maxLeafDepth`, `InsertionScheduleTree.depth_le_maxLeafDepth`, `InsertionScheduleTree.leafDepthWeights_depth_le_maxLeafDepth`, `InsertionScheduleTree.exists_deepest_sibling_leaf_pair` |
| Algorithm 4.1 materialization into insertion schedules | Higham §4.2, p. 91 | `SumTree.toInsertionScheduleTree`, `SumTree.toInsertionScheduleTree_eval`, `SumTree.toInsertionScheduleTree_exactEval`, `SumTree.toInsertionScheduleTree_leafCount`, `SumTree.toInsertionScheduleTree_leaves_nonnegative`, `SumTree.eval_exactWithUnitRoundoff`, `SumTree.runningErrorBudget_exactWithUnitRoundoff_eq_toInsertionScheduleTree_exactMergeCost`, `SumTree.runningErrorBudget_exactWithUnitRoundoff_eq_weightedLeafDepthCost_of_nonnegative` |
| Insertion finite two-smallest locator | Higham §4.2, p. 91 | `InsertionScheduleTree.exists_two_smallest_weight_decomposition`, `InsertionScheduleTree.exists_two_smallest_weight_decomposition_components` |
| Insertion same-shape relabeling realization | Higham §4.2, p. 91 | `InsertionScheduleTree.relabelLeaves`, `InsertionScheduleTree.relabelLeaves_leaves_eq`, `InsertionScheduleTree.relabelLeaves_leafDepthWeights_eq_zip`, `InsertionScheduleTree.exists_relabelLeaves_leafDepthWeights_eq_of_depths_eq`, `InsertionScheduleTree.exists_relabelLeaves_for_two_smallest_deepest_exchange_branch_of_depths_eq`, `InsertionScheduleTree.exists_tree_for_deepest_pair_noop_eq`, `InsertionScheduleTree.exists_tree_for_two_pair_exchange_of_two_smallest_decomposition_eq`, `InsertionScheduleTree.exists_tree_for_two_pair_exchange_reverse_of_two_smallest_decomposition_eq`, `InsertionScheduleTree.exists_tree_for_two_pair_exchange_before_deepest_of_two_smallest_decomposition_eq`, `InsertionScheduleTree.exists_tree_for_two_pair_exchange_reverse_before_deepest_of_two_smallest_decomposition_eq`, `InsertionScheduleTree.exists_tree_for_two_pair_exchange_around_deepest_of_two_smallest_decomposition_eq`, `InsertionScheduleTree.exists_tree_for_two_pair_exchange_reverse_around_deepest_of_two_smallest_decomposition_eq`, `InsertionScheduleTree.exists_tree_for_left_deepest_two_smallest_decomposition_eq`, `InsertionScheduleTree.exists_tree_for_right_deepest_two_smallest_decomposition_eq`, `InsertionScheduleTree.exists_tree_for_left_deepest_second_two_smallest_decomposition_eq`, `InsertionScheduleTree.exists_tree_for_right_deepest_second_two_smallest_decomposition_eq` |
| Recursive ordering example | Higham §4.2, example (4.5) | `IncreasingMagnitudeOrder`, `StrictIncreasingMagnitudeOrder`, `DecreasingMagnitudeOrder`, `StrictDecreasingMagnitudeOrder`, `fl_recursiveSumInOrder`, `sum_orderedInput_eq_sum`, `P91CancellationRounding`, `fl_p91Increasing_eq_zero`, `fl_p91Psum_eq_zero`, `fl_p91Decreasing_eq_one`, `p91Increasing_relError_eq_one`, `p91Psum_relError_eq_one`, `p91Increasing_runningErrorBudget_eq`, `p91Psum_runningErrorBudget_eq`, `p91Decreasing_runningErrorBudget_eq`, `p91_runningErrorBudget_ranking` |
| Correction formula trace | Higham §4.3, equation (4.7) | `CorrectionFormulaTrace`, `CorrectionFormulaTrace.exact`, `correctionFormulaTrace`, `correctionFormulaTrace_s`, `correctionFormulaTrace_e`, `FastTwoSumFiniteCertificate`, `FastTwoSumFiniteCertificate.finite_a_sub_s_of_signed_sterbenz`, `FastTwoSumFiniteCertificate.of_base2_abs_order_of_signed_sterbenz_a_sub_s`, `FastTwoSumFiniteCertificate.finite_a_sub_s_of_signed_sterbenz_or_endpoint`, `FastTwoSumFiniteCertificate.of_base2_abs_order_of_signed_sterbenz_or_endpoint_a_sub_s`, `FastTwoSumFiniteCertificate.finite_a_sub_s_of_signed_ratio_bounds`, `FastTwoSumFiniteCertificate.of_base2_abs_order_of_signed_ratio_bounds_a_sub_s`, `FastTwoSumFiniteCertificate.finite_a_sub_s_of_same_sign_abs_ratio_bounds`, `FastTwoSumFiniteCertificate.of_base2_abs_order_of_same_sign_abs_ratio_bounds_a_sub_s`, `FastTwoSumFiniteCertificate.finite_a_sub_s_of_same_sign_abs_order`, `FastTwoSumFiniteCertificate.of_base2_abs_order_of_same_sign_a_sub_s`, `correctionFormulaStrictSterbenzEndpointFormat`, `correctionFormulaStrictSterbenzEndpoint_round_one_add_three_quarters`, `correctionFormula_base2_abs_gt_inexact_not_imply_signed_sterbenz`, `finiteCorrectionFormulaTrace_exact_of_fastTwoSumFiniteCertificate`, `FloatingPointFormat.finiteRoundToEvenOp_add_normalized_sameSign_subnormal_error_finiteSystem_of_baseTwo`, `FloatingPointFormat.finiteRoundToEvenOp_add_subnormal_sameSign_normalized_error_finiteSystem_of_baseTwo`, `FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_finiteSystemWithSign_error_finiteSystem_of_baseTwo`, `FloatingPointFormat.finiteRoundToEvenOp_add_pos_neg_finiteSystemWithSign_eq_exact_of_sterbenzRatioCondition`, `FloatingPointFormat.finiteRoundToEvenOp_add_neg_pos_finiteSystemWithSign_eq_exact_of_sterbenzRatioCondition`, `FloatingPointFormat.finiteRoundToEvenOp_add_pos_neg_finiteSystemWithSign_error_finiteSystem_of_sterbenzRatioCondition`, `FloatingPointFormat.finiteRoundToEvenOp_add_neg_pos_finiteSystemWithSign_error_finiteSystem_of_sterbenzRatioCondition`, `FloatingPointFormat.finiteRoundToEvenOp_add_pos_neg_finiteSystemWithSign_eq_exact_of_magnitude_lt_two`, `FloatingPointFormat.finiteRoundToEvenOp_add_neg_pos_finiteSystemWithSign_eq_exact_of_magnitude_lt_two`, `FloatingPointFormat.finiteRoundToEvenOp_add_pos_neg_finiteSystemWithSign_error_finiteSystem_of_magnitude_lt_two`, `FloatingPointFormat.finiteRoundToEvenOp_add_neg_pos_finiteSystemWithSign_error_finiteSystem_of_magnitude_lt_two`, `FloatingPointFormat.finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_exponent_gap_gt_t`, `FloatingPointFormat.finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_exponent_gap_gt_t`, `FloatingPointFormat.finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_exponent_gap_eq_t`, `FloatingPointFormat.finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_exponent_gap_eq_t`, `FloatingPointFormat.finiteRoundToEvenOp_add_positive_min_neg_orderedExponent_error_finiteSystem_of_exponent_gap_gt_t_pred`, `FloatingPointFormat.finiteRoundToEvenOp_add_negative_min_pos_orderedExponent_error_finiteSystem_of_exponent_gap_gt_t_pred`, `FloatingPointFormat.finiteRoundToEvenOp_add_positive_min_neg_orderedExponent_error_finiteSystem_of_exponent_gap_eq_t_pred`, `FloatingPointFormat.finiteRoundToEvenOp_add_negative_min_pos_orderedExponent_error_finiteSystem_of_exponent_gap_eq_t_pred`, `FloatingPointFormat.finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_multiGuardComplementaryRegion`, `FloatingPointFormat.finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_multiGuardComplementaryRegion`, `FloatingPointFormat.finiteRoundToEvenOp_add_positive_normalized_neg_subnormal_error_finiteSystem_of_exponent_gap_ge_t`, `FloatingPointFormat.finiteRoundToEvenOp_add_negative_normalized_pos_subnormal_error_finiteSystem_of_exponent_gap_ge_t`, `FloatingPointFormat.finiteRoundToEvenOp_add_positive_min_normalized_neg_subnormal_error_finiteSystem_of_exponent_gap_ge_t_pred`, `FloatingPointFormat.finiteRoundToEvenOp_add_negative_min_normalized_pos_subnormal_error_finiteSystem_of_exponent_gap_ge_t_pred`, `FloatingPointFormat.finiteRoundToEvenOp_add_positive_normalized_neg_subnormal_error_finiteSystem_of_exponent_eq_emin_add_t_sub_one`, `FloatingPointFormat.finiteRoundToEvenOp_add_negative_normalized_pos_subnormal_error_finiteSystem_of_exponent_eq_emin_add_t_sub_one`, `FloatingPointFormat.finiteRoundToEvenOp_add_positive_min_normalized_neg_subnormal_error_finiteSystem_of_pred_exponent_eq_emin_add_t_sub_one`, `FloatingPointFormat.finiteRoundToEvenOp_add_negative_min_normalized_pos_subnormal_error_finiteSystem_of_pred_exponent_eq_emin_add_t_sub_one`, `FloatingPointFormat.finiteRoundToEvenOp_add_negative_subnormal_pos_normalized_error_finiteSystem_of_exponent_eq_emin_add_t_sub_one`, `FloatingPointFormat.finiteRoundToEvenOp_add_positive_subnormal_neg_normalized_error_finiteSystem_of_exponent_eq_emin_add_t_sub_one`, `FloatingPointFormat.finiteRoundToEvenOp_add_negative_subnormal_pos_min_normalized_error_finiteSystem_of_pred_exponent_eq_emin_add_t_sub_one`, `FloatingPointFormat.finiteRoundToEvenOp_add_positive_subnormal_neg_min_normalized_error_finiteSystem_of_pred_exponent_eq_emin_add_t_sub_one` |
| Correction formula near-magnitude inexact exclusions | Higham §4.3, equation (4.7) | `FloatingPointFormat.finiteSystemWithSign_false_of_finiteSystem_of_nonneg`, `FloatingPointFormat.finiteSystemWithSign_true_of_finiteSystem_of_nonpos`, `FloatingPointFormat.finiteRoundToEvenOp_add_pos_neg_finiteSystemWithSign_not_lt_two_of_ne_exact`, `FloatingPointFormat.finiteRoundToEvenOp_add_neg_pos_finiteSystemWithSign_not_lt_two_of_ne_exact`, `FloatingPointFormat.finiteRoundToEvenOp_add_pos_neg_finiteSystem_eq_exact_of_magnitude_lt_two`, `FloatingPointFormat.finiteRoundToEvenOp_add_neg_pos_finiteSystem_eq_exact_of_magnitude_lt_two`, `FloatingPointFormat.finiteRoundToEvenOp_add_pos_neg_finiteSystem_not_lt_two_of_ne_exact`, `FloatingPointFormat.finiteRoundToEvenOp_add_neg_pos_finiteSystem_not_lt_two_of_ne_exact` |
| Correction formula rounded-add interval bracketing | Higham §4.3, equation (4.7) | `FloatingPointFormat.finiteRoundToEvenOp_add_ge_of_finiteSystem_le_exact`, `FloatingPointFormat.finiteRoundToEvenOp_add_mem_Icc_of_finiteSystem_bounds` |
| Correction formula half-or-min-normal source split | Higham §4.3, equation (4.7) | `FloatingPointFormat.finiteSystem_half_or_le_two_minNormalMagnitude_of_nonneg_baseTwo` |
| Correction formula full finite binary exactness | Higham §4.3, equation (4.7) | `FastTwoSumFiniteCertificate.signed_ratio_bounds_of_pos_neg_abs_order_inexact`, `FastTwoSumFiniteCertificate.signed_ratio_bounds_of_neg_pos_abs_order_inexact`, `FastTwoSumFiniteCertificate.signed_ratio_bounds_of_opposite_sign_abs_order_inexact`, `FastTwoSumFiniteCertificate.of_base2_abs_order_of_opposite_sign_inexact_a_sub_s`, `FastTwoSumFiniteCertificate.of_base2_abs_gt_of_inexact_add`, `FastTwoSumFiniteCertificate.of_base2_abs_gt`, `finiteCorrectionFormulaTrace_exact_of_base2_abs_gt` |
| Correction formula same-sign first-sum interval bridge | Higham §4.3, equation (4.7) | `FastTwoSumFiniteCertificate.finite_a_sub_s_of_same_sign_first_sum_interval`, `FastTwoSumFiniteCertificate.of_base2_abs_order_of_same_sign_first_sum_interval_a_sub_s` |
| Correction formula same-sign small-addend branch | Higham §4.3, equation (4.7) | `FastTwoSumFiniteCertificate.finite_a_sub_s_of_same_sign_small_addend`, `FastTwoSumFiniteCertificate.of_base2_abs_order_of_same_sign_small_addend_a_sub_s` |
| Correction formula full same-sign branch | Higham §4.3, equation (4.7) | `FastTwoSumFiniteCertificate.finite_a_sub_s_of_same_sign_abs_order`, `FastTwoSumFiniteCertificate.of_base2_abs_order_of_same_sign_a_sub_s` |
| Correction formula opposite-sign exact/one-guard branch | Higham §4.3, equation (4.7) | `FloatingPointFormat.finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_alignedDiffCoeff_lt_two_mul_mantissaBound`, `FloatingPointFormat.finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_alignedDiffCoeff_lt_two_mul_mantissaBound` |
| Correction formula opposite-sign non-min high dispatcher | Higham §4.3, equation (4.7) | `FloatingPointFormat.finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_baseTwo_nonMinHigh`, `FloatingPointFormat.finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_baseTwo_nonMinHigh` |
| Correction formula opposite-sign min-high dispatcher | Higham §4.3, equation (4.7) | `FloatingPointFormat.finiteRoundToEvenOp_add_positive_min_neg_orderedExponent_error_finiteSystem_of_alignedDiffCoeff_lt_two_mul_or_pred_exponent_gap_ge_t`, `FloatingPointFormat.finiteRoundToEvenOp_add_negative_min_pos_orderedExponent_error_finiteSystem_of_alignedDiffCoeff_lt_two_mul_or_pred_exponent_gap_ge_t`, `FloatingPointFormat.alignedDiffCoeff_minNormalMantissa_lt_two_precision_bound_of_exponent_gap_eq_t`, `FloatingPointFormat.finiteRoundToEvenOp_add_positive_min_neg_orderedExponent_error_finiteSystem_of_baseTwo`, `FloatingPointFormat.finiteRoundToEvenOp_add_negative_min_pos_orderedExponent_error_finiteSystem_of_baseTwo` |
| Correction formula opposite-sign normalized-system integration | Higham §4.3, equation (4.7) | `FloatingPointFormat.normalizedMantissa_le_scaled_of_exponent_lt`, `FloatingPointFormat.finiteRoundToEvenOp_add_positive_neg_normalized_error_finiteSystem_of_baseTwo`, `FloatingPointFormat.finiteRoundToEvenOp_add_negative_pos_normalized_error_finiteSystem_of_baseTwo`, `FloatingPointFormat.finiteRoundToEvenOp_add_pos_neg_normalizedSystem_error_finiteSystem_of_baseTwo`, `FloatingPointFormat.finiteRoundToEvenOp_add_neg_pos_normalizedSystem_error_finiteSystem_of_baseTwo` |
| Correction formula mixed opposite-sign aligned-difference exact branch | Higham §4.3, equation (4.7) | `FloatingPointFormat.normalizedValue_add_positive_neg_subnormal_finiteSystem_of_alignedDiffCoeff_lt_mantissaBound`, `FloatingPointFormat.normalizedValue_add_negative_pos_subnormal_finiteSystem_of_alignedDiffCoeff_lt_mantissaBound`, `FloatingPointFormat.finiteRoundToEvenOp_add_positive_normalized_neg_subnormal_error_finiteSystem_of_alignedDiffCoeff_lt_mantissaBound`, `FloatingPointFormat.finiteRoundToEvenOp_add_negative_normalized_pos_subnormal_error_finiteSystem_of_alignedDiffCoeff_lt_mantissaBound`, `FloatingPointFormat.finiteRoundToEvenOp_add_negative_subnormal_pos_normalized_error_finiteSystem_of_alignedDiffCoeff_lt_mantissaBound`, `FloatingPointFormat.finiteRoundToEvenOp_add_positive_subnormal_neg_normalized_error_finiteSystem_of_alignedDiffCoeff_lt_mantissaBound` |
| Correction formula mixed opposite-sign base-2 dispatcher | Higham §4.3, equation (4.7) | `FloatingPointFormat.subnormalMantissa_le_aligned_normalizedCoeff`, `FloatingPointFormat.sourceRoundToEvenEvidence_positive_normalizedValue_add_neg_subnormal_error_finiteSystem_of_guardCoeffBounds`, `FloatingPointFormat.sourceRoundToEvenEvidence_negative_normalizedValue_add_pos_subnormal_error_finiteSystem_of_guardCoeffBounds`, `FloatingPointFormat.mixedAlignedDiffCoeff_lt_two_precision_bound_of_normalized_subnormal_window`, `FloatingPointFormat.finiteRoundToEvenOp_add_positive_normalized_neg_subnormal_error_finiteSystem_of_multiGuardComplementaryRegion`, `FloatingPointFormat.finiteRoundToEvenOp_add_negative_normalized_pos_subnormal_error_finiteSystem_of_multiGuardComplementaryRegion`, `FloatingPointFormat.finiteRoundToEvenOp_add_positive_normalized_neg_subnormal_error_finiteSystem_of_baseTwo`, `FloatingPointFormat.finiteRoundToEvenOp_add_negative_normalized_pos_subnormal_error_finiteSystem_of_baseTwo`, `FloatingPointFormat.finiteRoundToEvenOp_add_negative_subnormal_pos_normalized_error_finiteSystem_of_baseTwo`, `FloatingPointFormat.finiteRoundToEvenOp_add_positive_subnormal_neg_normalized_error_finiteSystem_of_baseTwo` |
| Correction formula broad rounded-add error dispatcher | Higham §4.3, equation (4.7) | `FloatingPointFormat.finiteRoundToEvenOp_add_finiteSystem_error_finiteSystem_of_baseTwo`, `FloatingPointFormat.finiteRoundToEvenOp_add_error_finite_of_base2_abs_order_of_finiteNormalRange` |
| No-guard correction formula counterexample | Higham §4.3, pp. 94--95 | `NoGuardCorrectionFormulaTrace`, `NoGuardCorrectionFormulaTrace.model`, `noGuardCorrectionFormulaTrace`, `noGuardCorrectionFormulaTrace_model`, `noGuardCorrectionFormulaCounterexample_model`, `noGuardCorrectionFormulaCounterexample_not_exact` |
| Kahan compensated summation trace | Higham §4.3, Algorithm 4.2 and p. 93 final correction | `KahanState`, `KahanStepTrace`, `kahanStepTrace`, `KahanStepDeltaWitness`, `exists_kahanStepTrace_deltaWitness`, `kahanStepTrace_deltaWitness`, `kahanStepDeltaWitness_s_expanded`, `kahanStepDeltaWitness_e_expanded`, `kahanStepDeltaWitness_e_fully_expanded`, `kahanStepDeltaWitness_total_fully_expanded`, `kahanTrace_deltaWitness`, `kahanTrace_deltaWitness_y`, `kahanTrace_deltaWitness_s`, `kahanTrace_deltaWitness_sub`, `kahanTrace_deltaWitness_e`, `kahanTrace_deltaWitness_s_expanded`, `kahanTrace_deltaWitness_e_expanded`, `kahanTrace_deltaWitness_e_fully_expanded`, `kahanTrace_deltaWitness_total_fully_expanded`, `kahanTrace_deltaWitness_deltaY_bound`, `kahanTrace_deltaWitness_deltaS_bound`, `kahanTrace_deltaWitness_deltaSub_bound`, `kahanTrace_deltaWitness_deltaE_bound`, `kahanStepTrace_e`, `kahanPrefixState`, `kahanTrace`, `fl_kahanState`, `fl_kahanSum`, `fl_kahanCorrection`, `fl_kahanFinalCorrectedSum` |
| Kahan finite-format exact first step | Higham §4.3, Algorithm 4.2 dependency | `finiteKahanStepTrace_zero_of_finiteSystem`, `finiteKahanStep_zero_of_finiteSystem`, and `finiteKahanPrefixState_one_of_finiteSystem` prove that a finite representable input starts exactly from `s = 0; e = 0` in the concrete finite round-to-even wrapper, exposing a finite-format/coherence fact not assumed by the bare abstract `FPModel`. |
| Kahan bare-model exact-start counterexample | Higham §4.3, Algorithm 4.2 dependency audit | `kahanStepTrace_abstractCounterexample_zero`, `kahanStep_abstractCounterexample_zero_ne_exact`, and `not_forall_kahanStep_zero_exact` show that the abstract `FPModel` interface alone does not force the first Kahan step from `s = 0; e = 0` to return `{s := x, e := 0}`. |
| Kahan bare-model returned-bound route elimination | Higham §4.3, equation (4.8) dependency audit | `kahanBiasedSmallCounterexampleFPModel`, `kahanBiasedTwoStepInput`, `fl_kahanSum_biasedSmallCounterexample_twoStep`, `fl_kahanSum_biasedSmallCounterexample_twoStep_of_pos_lt_one`, `not_exists_fl_kahanSum_biasedSmallCounterexample_twoStep_source_bound_of_Cu_le_half`, and `not_forall_fl_kahanSum_backward_error_source_bound_bare_fpmodel_exactSubConstants` show that a small-unit-roundoff abstract `FPModel` can satisfy the local relative-error contract while the returned value on `[1,0]` exceeds any `2*u+C*u^2` coefficient cap when `C*u <= 1/2`, including the exact-subtraction-route constants; the source-strength returned theorem therefore needs finite-format/coherence structure or a genuinely stronger non-FastTwoSum coefficient argument, not the bare model alone. |
| Kahan abstract exact-zero-path bridge | Higham §4.3, Algorithm 4.2 dependency | `kahanStepTrace_zero_of_exact_zero_path`, `kahanStep_zero_of_exact_zero_path`, and `kahanPrefixState_one_of_exact_zero_path` isolate the exact right-zero, `0-x`, and `(-x)+x` operation hypotheses sufficient for the source first-step initialization. |
| Kahan compensated-total coefficient bridge | Higham §4.3, eqs. (4.8)--(4.9) dependency | `kahanTotalStateCoeff`, `kahanTotalInputCoeff`, `kahanStepDeltaWitness_total_coefficients`, `kahanTrace_deltaWitness_total_coefficients` |
| Kahan per-step coefficient-radius bridge | Higham §4.3, eqs. (4.8)--(4.9) dependency | `kahanTotalStateCoeff_eq_one_sub_second_order`, `kahanTotalInputCoeff_eq_first_second_order`, `kahanTotalInputCoeff_sub_one_eq`, `kahanTotalStateCoeff_abs_sub_one_le`, `kahanTotalInputCoeff_abs_sub_one_le` |
| Kahan small-u local coefficient-collapse bridge | Higham §4.3, eqs. (4.8)--(4.9) dependency | `kahanTotalStateCoeff_abs_sub_one_le_three_u_sq`, `kahanTotalInputCoeff_abs_sub_one_le_two_u_plus_nine_u_sq`, `kahanTotalInputCoeff_abs_sub_one_le_two_u_plus_nine_n_u_sq` |
| Kahan retained-correction residual bridge | Higham §4.3, eqs. (4.8)--(4.9) dependency | `kahanTotalResidualCoeff`, `kahanStepDeltaWitness_total_compensated_total_coefficients`, `kahanTrace_deltaWitness_total_compensated_total_coefficients`, `kahanTotalResidualCoeff_abs_le_two_u_plus_twelve_u_sq`, `kahanTotalResidualCoeff_abs_le_two_u_plus_twelve_n_u_sq` |
| Kahan residual-aware affine product unroll | Higham §4.3, eqs. (4.8)--(4.9) dependency | `KahanAffineCoeffStep`, `KahanAffineCoeffStep.source`, `kahanAffineCoeffTailProd`, `kahanAffineResidualUnroll`, `kahanAffineResidualFold`, `kahanAffineResidualFold_eq_tailProd_mul_init_add_unroll`, `kahanAffineResidualFold_zero_eq_unroll` |
| Kahan prefix-trace coefficient-step instantiation | Higham §4.3, eqs. (4.8)--(4.9) dependency | `kahanAffineCoeffStepOfIndex`, `kahanTrace_total_eq_affineCoeffStep`, `kahanAffineCoeffSteps`, `kahanAffineCoeffSteps_fold_eq_finFold`, `kahanAffineCoeffSteps_finFold_eq_prefix_total`, `kahanAffineCoeffSteps_fold_zero_eq_prefix_total`, `kahanAffineCoeffSteps_fold_zero_eq_final_total` |
| Kahan retained-correction source split and local source bound | Higham §4.3, eqs. (4.8)--(4.9) dependency | `KahanAffineCoeffStep.inputSource`, `KahanAffineCoeffStep.correctionSource`, `KahanAffineCoeffStep.source_eq_input_add_correction`, `kahanAffineInputUnroll`, `kahanAffineCorrectionUnroll`, `kahanAffineCorrectionAbsUnroll`, `kahanAffineResidualUnroll_eq_input_add_correction`, `kahanAffineResidualFold_zero_eq_input_add_correction`, `kahanAffineCorrectionUnroll_abs_le`, `kahanAffineCoeffStepOfIndex_R_abs_le_two_u_plus_twelve_u_sq`, `kahanAffineCoeffStepOfIndex_correctionSource_abs_le` |
| Kahan old-total tail-product bound | Higham §4.3, eqs. (4.8)--(4.9) dependency | `kahanAffineCoeffTailProd_abs_le_pow`, `kahanAffineCoeffStepOfIndex_A_abs_le_one_plus_three_u_sq`, `kahanAffineCoeffSteps_A_abs_le_one_plus_three_u_sq`, `kahanAffineCoeffSteps_tailProd_abs_le_one_plus_three_u_sq_pow` |
| Kahan retained-correction local recurrence bound | Higham §4.3, eqs. (4.8)--(4.9) dependency | `kahanCorrectionStateCoeff`, `kahanCorrectionInputCoeff`, `kahanStepDeltaWitness_e_coefficients`, `kahanCorrectionStateCoeff_abs_le`, `kahanCorrectionInputCoeff_abs_le`, `kahanStepDeltaWitness_e_abs_le`, `kahanStepDeltaWitness_e_abs_le_split`, `kahanTrace_e_abs_le`, `kahanTrace_e_abs_le_split` |
| Kahan retained-correction prefix recurrence majorant | Higham §4.3, eqs. (4.8)--(4.9) dependency | `kahanCorrectionAbsMajorant`, `kahanCorrectionAbsMajorant_nonneg`, `kahanPrefixState_e_abs_le_correctionMajorant` |
| Kahan coupled input-only retained-correction majorants | Higham §4.3, eqs. (4.8)--(4.9) dependency | `kahanStepDeltaWitness_s_abs_le_inputMajorants`, `kahanInputAbsMajorant`, `kahanInputAbsMajorant_nonneg`, `kahanPrefixState_abs_le_inputMajorant`, `kahanPrefixState_s_abs_le_inputMajorant`, `kahanPrefixState_e_abs_le_inputMajorant` |
| Kahan propagated correction-source input-only budget | Higham §4.3, eqs. (4.8)--(4.9) dependency | `kahanAffineCorrectionIndexedBudget`, `kahanAffineCorrectionAbsUnroll_le_indexedBudget`, `kahanAffineCoeffStepOfIndex_correctionSource_abs_le_inputMajorant`, `kahanAffineCoeffSteps_correctionAbsUnroll_le_inputMajorantBudget` |
| Kahan input-coefficient residual bridge | Higham §4.3, eqs. (4.8)--(4.9) dependency | `kahanAffineInputCoeff`, `kahanAffineInputUnroll_eq_sum_inputCoeff`, `kahanAffineResidualFold_zero_eq_sum_inputCoeff_add_correction`, `kahanAffineResidualFold_zero_sub_sum_inputCoeff_abs_le`, `kahanAffineCoeffSteps_prefixTotal_sub_sum_inputCoeff_abs_le_inputMajorantBudget` |
| Kahan returned-sum residual absorption | Higham §4.3, eqs. (4.8)--(4.9) dependency | `summationAbsSign`, `exists_summation_coefficients_of_abs_sub_sum_coeff_le`, `kahanAffineCoeffSteps_prefixTotal_exists_mu_inputCoeffResidual`, `kahanAffineCoeffSteps_prefixSum_sub_sum_inputCoeff_abs_le_inputMajorantBudget`, `kahanAffineCoeffSteps_prefixSum_exists_mu_inputCoeffResidual` |
| Kahan product-radius coefficient witnesses | Higham §4.3, eqs. (4.8)--(4.9) dependency | `kahanAffineCoeffTailProd_abs_sub_one_le_pow_sub_one`, `kahanAffineInputCoeff_abs_le_productRadius`, `kahanAffineCoeffStepOfIndex_A_abs_sub_one_le_three_u_sq`, `kahanAffineCoeffStepOfIndex_B_abs_sub_one_le_two_u_plus_nine_u_sq`, `kahanAffineCoeffSteps_A_abs_sub_one_le_three_u_sq`, `kahanAffineCoeffSteps_B_abs_sub_one_le_two_u_plus_nine_u_sq`, `kahanAffineInputCoeffProductRadius`, `kahanAffineCoeffSteps_inputCoeff_abs_le_productRadius`, `kahanAffineCoeffSteps_prefixSum_exists_mu_abs_le_productRadius` |
| Kahan product-radius concrete collapse | Higham §4.3, eqs. (4.8)--(4.9) dependency | `one_add_pow_sub_one_le_two_mul_nat_mul_of_nat_mul_le_half`, `kahanAffineInputCoeffProductRadius_le_two_u_plus` |
| Kahan affine residual-budget returned theorem | Higham §4.3, equation (4.8) conditional dependency/rejected route | `kahanAffineCoeffSteps_prefixSum_exists_mu_abs_le_of_productRadius_and_residualBudget` and `fl_kahanSum_backward_error_source_bound_of_affine_residualBudget` prove the returned-sum source bound from a product-radius bound plus a source-scaled retained-correction residual estimate `C*n*u^2*sum_i |x_i|`. The route audit theorems `not_kahanAffine_residualBudget_inputMajorant_one_of_Cu_le_one` and `not_exists_kahanAffine_residualBudget_inputMajorant_fixed_C` show the current input-only retained-correction majorant cannot supply that estimate with any fixed nonnegative `C`; the remaining affine work must refine the residual, prove coefficient cancellation directly, or use stronger finite-format/coherence hypotheses. |
| Kahan direct stored-sum coefficient bridge | Higham §4.3, eqs. (4.8)--(4.9) dependency | `kahanStoredSumStateCoeff`, `kahanStoredSumInputCoeff`, `kahanStepDeltaWitness_s_coefficients`, `kahanStoredSumStateCoeff_abs_sub_one_le`, `kahanStoredSumInputCoeff_sub_one_eq`, `kahanStoredSumInputCoeff_sub_stateCoeff_eq`, `kahanStoredSumInputCoeff_abs_sub_one_le_two_u_plus_u_sq`, `kahanStoredSumInputCoeff_sub_stateCoeff_abs_le_u_mul_one_add_u`, `kahanTrace_deltaWitness_s_coefficients`, `kahanTrace_deltaWitness_storedSumInputCoeff_abs_sub_one_le_two_u_plus_u_sq` |
| Kahan exact coupled prefix-state recursion | Higham §4.3, eqs. (4.8)--(4.9) dependency | `KahanState.ext_state`, `KahanState.add`, `KahanState.smul`, `kahanTrace_deltaWitness_e_coefficients`, `KahanCoupledCoeffStep`, `KahanCoupledCoeffStep.next`, `KahanCoupledCoeffStep.propagate`, `KahanCoupledCoeffStep.source`, `KahanCoupledCoeffStep.sourceCoeff`, `KahanCoupledCoeffStep.next_eq_propagate_add_source`, `KahanCoupledCoeffStep.source_eq_smul_sourceCoeff`, `KahanCoupledCoeffStep.propagate_add`, `KahanCoupledCoeffStep.propagate_smul`, `kahanCoupledCoeffFold`, `kahanCoupledExactZeroStep`, `kahanCoupledExactZeroStep_next`, `kahanCoupledExactZeroStep_propagate`, `kahanCoupledCoeffFold_append_exactZeroStep`, `kahanCoupledCoeffPropagate_append_exactZeroStep`, `kahanCoupledCoeffStepOfIndex`, `kahanTrace_eq_coupledCoeffStep_next`, `kahanCoupledCoeffSteps`, `kahanCoupledCoeffSteps_fold_eq_finFold`, `kahanCoupledCoeffSteps_finFold_eq_prefix_state`, `kahanCoupledCoeffSteps_fold_zero_eq_prefix_state` |
| Kahan coupled source-vector unroll | Higham §4.3, eqs. (4.8)--(4.9) dependency | `kahanCoupledCoeffPropagate`, `kahanCoupledSourceUnroll`, `kahanCoupledCoeffPropagate_add`, `kahanCoupledCoeffPropagate_smul`, `kahanCoupledCoeffPropagate_zero`, `kahanCoupledCoeffFold_eq_propagate_add_sourceUnroll`, `kahanCoupledCoeffFold_zero_eq_sourceUnroll`, `kahanCoupledCoeffPropagate_append_exactZeroStep`, `kahanCoupledSourceUnroll_append_exactZeroStep`, `kahanCoupledSourceCoeff_append_exactZeroStep_s_eq_sourceTotalCoeff`, `kahanCoupledSourceCoeff_append_exactZeroStep_e_eq_zero`, `kahanCoupledCoeffSteps_sourceUnroll_eq_prefix_state` |
| Kahan coupled returned-sum scalar coefficient extraction | Higham §4.3, eqs. (4.8)--(4.9) dependency | `kahanCoupledSourceCoeff`, `kahanCoupledSourceUnroll_s_eq_sum_sourceCoeff`, `kahanCoupledCoeffSteps_prefixState_s_eq_sum_sourceCoeff` |
| Kahan coupled paired-total coefficient extraction | Higham §4.3, eqs. (4.8)--(4.9) dependency | `kahanCoupledSourceUnroll_e_eq_sum_sourceCoeff`, `kahanCoupledSourceTotalCoeff`, `kahanCoupledSourceUnroll_total_eq_sum_sourceTotalCoeff`, `kahanCoupledCoeffSteps_prefixState_e_eq_sum_sourceCoeff`, `kahanCoupledCoeffSteps_prefixState_total_eq_sum_sourceTotalCoeff` |
| Kahan coupled paired-total local coefficient handoff | Higham §4.3, eqs. (4.8)--(4.9) dependency | `KahanCoupledCoeffStep.totalStateCoeff`, `KahanCoupledCoeffStep.totalInputCoeff`, `KahanCoupledCoeffStep.residualCoeff`, `KahanCoupledCoeffStep.next_total_eq_compensated_total`, `kahanCoupledCoeffStepOfIndex_totalStateCoeff_eq`, `kahanCoupledCoeffStepOfIndex_totalInputCoeff_eq`, `kahanCoupledCoeffStepOfIndex_residualCoeff_eq`, `kahanCoupledCoeffStepOfIndex_totalStateCoeff_abs_sub_one_le_three_u_sq`, `kahanCoupledCoeffStepOfIndex_totalInputCoeff_abs_sub_one_le_two_u_plus_nine_u_sq`, `kahanCoupledCoeffStepOfIndex_residualCoeff_abs_le_two_u_plus_twelve_u_sq`, `kahanCoupledCoeffSteps_totalStateCoeff_abs_sub_one_le_three_u_sq`, `kahanCoupledCoeffSteps_totalInputCoeff_abs_sub_one_le_two_u_plus_nine_u_sq`, `kahanCoupledCoeffSteps_residualCoeff_abs_le_two_u_plus_twelve_u_sq` |
| Kahan paired-coordinate source propagation | Higham §4.3, eqs. (4.8)--(4.9) dependency | `KahanState.totalCorrection`, `KahanCoupledCoeffStep.correctionResidualCoeff`, `KahanCoupledCoeffStep.propagateTotalCorrection`, `KahanCoupledCoeffStep.sourceCoeff_totalCorrection`, `KahanCoupledCoeffStep.propagate_totalCorrection`, `kahanCoupledTotalCorrectionPropagate`, `kahanCoupledCoeffPropagate_totalCorrection_eq`, `kahanCoupledSourceTotalCorrectionCoeff`, `kahanCoupledSourceCoeff_totalCorrection_eq`, `kahanCoupledSourceTotalCoeff_eq_totalCorrectionPropagate_s`, `kahanCoupledSourceCoeff_e_eq_totalCorrectionPropagate_e`, `kahanCoupledCoeffStepOfIndex_C_abs_le`, `kahanCoupledCoeffStepOfIndex_D_abs_le`, `kahanCoupledCoeffStepOfIndex_correctionResidualCoeff_abs_le`, `kahanCoupledCoeffSteps_C_abs_le`, `kahanCoupledCoeffSteps_D_abs_le`, `kahanCoupledCoeffSteps_correctionResidualCoeff_abs_le` |
| Kahan returned source-coordinate bridge | Higham §4.3, equation (4.8) dependency | `kahanCoupledSourceCoeff_s_eq_returned_totalCorrectionPropagate` identifies the ordinary returned source coefficient as the returned coordinate of the paired `(s+e,e)` propagated source coefficient. |
| Kahan returned coefficient triangle-route bound | Higham §4.3, equation (4.8) rejected-route audit | `kahanCoupledSourceCoeff_s_abs_sub_one_le_pairedCoeffMajorant_sum` and `kahanCoupledCoeffSteps_sourceCoeff_s_abs_sub_one_le_pairedCoeffMajorant_sum` formalize the triangle bound through paired total plus retained correction; this bound is intentionally recorded as too weak for the source `2*u + O(n*u^2)` result. |
| Kahan exact-sub returned coefficient route | Higham §4.3, equation (4.8) conditional dependency | `kahanCoupledCoeffStepsExactSub`, the `..._of_deltaSub_zero` local coefficient bounds, `kahanCoupledPairedCoeffMajorant_exactSubConstants_le_one_u_plus`, `kahanCoupledSourceCoeff_s_abs_sub_one_le_exactSubMajorant`, and `kahanCoupledCoeffSteps_sourceCoeff_s_abs_sub_one_le_two_u_plus_exactSubMajorant` prove the source-shaped ordinary returned coefficient bound under the explicit hypothesis that every correction-subtraction delta in the prefix is zero. |
| Kahan exact-sub witness-family route | Higham §4.3, equation (4.8) conditional dependency | `exists_kahanStepTrace_deltaWitness_of_exact_sub`, `kahanStepTrace_deltaWitnessOfExactSub`, `KahanPrefixCorrectionSubExact`, `kahanPrefixDeltaWitnessFamilyOfExactSub`, `kahanPrefixDeltaWitnessFamilyOfExactSub_exactSub`, `kahanCoupledCoeffStepOfWitness`, `KahanPrefixDeltaWitnessFamily`, `kahanCoupledCoeffStepsOfWitnesses`, the witness-family exact-sub list bounds, `kahanCoupledCoeffStepsOfWitnesses_sourceCoeff_s_abs_sub_one_le_two_u_plus_exactSubMajorant`, `kahanCoupledCoeffStepsOfWitnesses_prefixState_s_eq_sum_sourceCoeff`, `KahanAddSubFiniteRoundToEvenRealization`, `finiteKahanTrace_temp_finiteSystem`, `finiteKahanTrace_y_finiteSystem`, `FiniteKahanPrefixCorrectionSubFinite`, `FiniteKahanPrefixCorrectionSubFinite.of_first_exact_and_tail_sub_finite`, `KahanPrefixFastTwoSumFiniteCertificates`, `KahanPrefixFastTwoSumFiniteCertificates.of_base2_abs_gt`, `KahanPrefixFastTwoSumFiniteCertificates.of_first_exact_and_tail_base2_abs_gt`, `KahanPrefixCorrectionSubExact.of_finiteRoundToEven_fastTwoSumCertificates`, `fl_kahanSum_backward_error_source_bound_of_exactSubWitnesses`, `fl_kahanSum_backward_error_source_bound_of_exactSubTrace`, `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_tail_sub_finite`, `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_fastTwoSumCertificates`, `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_base2_abs_gt`, `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_base2_abs_gt_of_order_range`, `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_base2_tail_order_range`, `not_forall_finiteKahanTrace_tail_abs_order`, `not_forall_finiteKahanTrace_tail_sterbenzLe`, `not_forall_finiteKahanTrace_tail_fergusonLe`, and `not_forall_finiteKahanTrace_tail_direct_sub_finite` package the returned-sum backward-error theorem under direct tail finite correction-subtraction, finite-format FastTwoSum correction-subtraction certificates, or base-2 order/range hypotheses, with the initialized first step handled by finite zero-add exactness or `temp = 0`; the final counterexamples record that tail order, tail inclusive Sterbenz, tail inclusive Ferguson, and direct tail finite subtraction are not derivable for arbitrary input order. |
| Kahan finite/coherence correction-subtraction routes | Higham §4.3, equation (4.8) conditional dependency | `finiteKahanTrace_s_finiteSystem`, `FiniteKahanPrefixCorrectionSubFinite.of_first_exact_and_tail_sub_finite`, `FiniteKahanPrefixCorrectionSubFinite.of_sterbenzRatioConditionLe`, `FiniteKahanPrefixCorrectionSubFinite.of_fergusonConditionLe`, `FiniteKahanPrefixCorrectionSubFinite.of_first_exact_and_tail_sterbenzLe`, `FiniteKahanPrefixCorrectionSubFinite.of_first_exact_and_tail_fergusonLe`, `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_sub_finite`, `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_tail_sub_finite`, `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_sterbenzLe`, `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_fergusonLe`, `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_tail_sterbenzLe`, `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_tail_fergusonLe`, `not_forall_finiteKahanTrace_tail_sterbenzLe`, `not_forall_finiteKahanTrace_tail_fergusonLe`, and `not_forall_finiteKahanTrace_tail_direct_sub_finite` expose non-FastTwoSum finite-format branches: finite correction-subtraction representability, direct tail finite correction-subtraction, inclusive Sterbenz/Ferguson conditions, or tail-only Sterbenz/Ferguson conditions with the first trace index closed automatically by `temp = 0`, each composing into the same source-shaped returned-sum theorem. `FloatingPointFormat.not_forall_finiteSystem_sub_finiteSystem` rules out closing this route from finite-coordinate hypotheses alone, while `not_forall_finiteKahanTrace_tail_sterbenzLe`, `not_forall_finiteKahanTrace_tail_fergusonLe`, and `not_forall_finiteKahanTrace_tail_direct_sub_finite` rule out deriving tail inclusive Sterbenz, tail inclusive Ferguson, or direct tail finite correction-subtraction for arbitrary input order. These remain conditional routes, not the arbitrary-input Eq. (4.8) closure. |
| Kahan returned-coordinate obstruction surface | Higham §4.3, eq. (4.8) dependency | `KahanState.returnedFromTotalCorrection`, `KahanState.returnedFromTotalCorrection_totalCorrection`, `KahanCoupledCoeffStep.returnedStateCoeff`, `KahanCoupledCoeffStep.returnedCorrectionCoeff`, `KahanCoupledCoeffStep.returnedStateCoeff_eq_A`, `KahanCoupledCoeffStep.returnedCorrectionCoeff_eq_B_sub_A`, `KahanCoupledCoeffStep.propagateTotalCorrection_returned`, `KahanCoupledCoeffStep.propagateTotalCorrection_returnedDev_abs_le_of_bounds`, `kahanCoupledCoeffStepOfIndex_returnedStateCoeff_abs_sub_one_le`, `kahanCoupledCoeffStepOfIndex_returnedCorrectionCoeff_abs_le`, `kahanCoupledCoeffSteps_returnedStateCoeff_abs_sub_one_le`, `kahanCoupledCoeffSteps_returnedCorrectionCoeff_abs_le`, `kahanCoupledCoeffSteps_propagateTotalCorrection_returnedDev_abs_le` |
| Kahan returned-sum conditional backward witness | Higham §4.3, eq. (4.8) dependency | `fl_kahanSum_backward_error_source_bound_of_sourceCoeff_s_bound` and `fl_kahanSum_backward_error_source_bound_of_witnessSourceCoeff_s_bound` turn source-shaped returned-coefficient bounds into the ordinary returned-sum backward-error representation; `fl_kahanSum_backward_error_source_bound_of_exactSubWitnesses`, `fl_kahanSum_backward_error_source_bound_of_exactSubTrace`, `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_sub_finite`, `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_tail_sub_finite`, `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_sterbenzLe`, `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_fergusonLe`, `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_tail_sterbenzLe`, `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_tail_fergusonLe`, `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_fastTwoSumCertificates`, `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_base2_abs_gt`, `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_base2_abs_gt_of_order_range`, and `fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_base2_tail_order_range` compose the exact-sub coefficient bound with finite/coherence hypotheses. `not_forall_finiteKahanTrace_tail_abs_order`, `not_forall_finiteKahanTrace_tail_sterbenzLe`, `not_forall_finiteKahanTrace_tail_fergusonLe`, and `not_forall_finiteKahanTrace_tail_direct_sub_finite` show the tail-order, tail-Sterbenz, tail-Ferguson, and direct tail finite-subtraction bridges are conditional only and cannot close the arbitrary-input source theorem. |
| Kahan paired-coordinate majorant induction substrate | Higham §4.3, eqs. (4.8)--(4.9) dependency | `KahanCoupledCoeffStep.propagateTotalCorrection_totalDev_abs_le`, `KahanCoupledCoeffStep.propagateTotalCorrection_totalDev_abs_le_of_bounds`, `KahanCoupledCoeffStep.propagateTotalCorrection_correction_abs_le`, `KahanCoupledCoeffStep.propagateTotalCorrection_correction_abs_le_of_bounds`, `kahanCoupledPairedCoeffMajorant`, `kahanCoupledPairedCoeffMajorant_nonneg`, `kahanCoupledPairedCoeffMajorant_exactSubConstants_le_one_u_plus`, `kahanCoupledTotalCorrectionPropagate_abs_le_pairedCoeffMajorant`, `kahanCoupledSourceTotalCorrectionCoeff_abs_le_pairedCoeffMajorant`, `kahanCoupledCoeffSteps_propagateTotalCorrection_totalDev_abs_le`, `kahanCoupledCoeffSteps_propagateTotalCorrection_correction_abs_le`, `kahanCoupledCoeffSteps_propagateTotalCorrection_totalDev_abs_le_of_exactSub`, `kahanCoupledCoeffSteps_propagateTotalCorrection_correction_abs_le_of_exactSub`, `kahanCoupledCoeffSteps_totalCorrectionPropagate_abs_le_pairedCoeffMajorant`, `kahanCoupledCoeffSteps_sourceTotalCorrectionCoeff_abs_le_pairedCoeffMajorant` |
| Kahan paired-total majorant collapse | Higham §4.3, eqs. (4.8)--(4.9) dependency | `kahanCoupledPairedCoeffMajorant_kahanConstants_le_two_u_plus`, `kahanCoupledCoeffSteps_sourceTotalCoeff_abs_sub_one_le_two_u_plus_majorant` |
| Kahan compensated-total backward witness | Higham §4.3, eqs. (4.8)--(4.9) dependency | `fl_kahanCompensatedTotal_backward_error_source_bound` proves a source-shaped backward-error representation for the retained compensated total `(fl_kahanState fp n v).s + (fl_kahanState fp n v).e`; the ordinary returned-sum equation (4.8) remains separately open. |
| Shewchuk local addition error | Higham Chapter 4, Problem 4.6 | `FloatingPointFormat.nearestRoundingToFinite_add_abs_error_le_min_of_finiteSystem`, `FloatingPointFormat.finiteRoundToEvenOp_add_abs_error_le_min_of_finiteSystem`, `FloatingPointFormat.finiteRoundToEvenOp_add_error_finite_of_base2_abs_order_of_finiteNormalRange` |
| Problem 4.10 Priest research example replay | Higham Chapter 4, Problem 4.10 | Experiment-only artifact `experiments/chapter04/problem49_priest_binary32_trace.py`; formal subclaims are the source-correct aliases `problem410PriestInput`, `problem410PriestInput_sum_eq_two`, `problem410PriestInput_t24_sum_eq_two`, `problem410PriestInput_t24_values`, `problem410PriestInput_t24_ieeeSingle_finiteSystem`, and `problem410PriestInput_t24_first_sum_ieeeSingle_rounds_to_67108864` |
| Alternative compensated summation trace and Eq. (4.10) transfer | Higham §4.3, p. 94, equation (4.10) | `AlternativeCompensatedStepTrace`, `alternativeCompensatedStepTrace`, `alternativeCompensatedPrefixSum`, `alternativeCompensatedTrace`, `alternativeCompensatedCorrections`, `alternativeCompensatedPrefixSum_eq_fl_recursiveSum_prefix`, `alternativeCompensatedTrace_main_add_input_eq_fl_partialSums`, `alternativeCompensatedPrefixCorrections_abs_le_recursiveSum_forward`, `alternativeCompensatedPrefixCorrections_abs_le_recursiveSum_forward_of_full_exact`, `fl_partialSums_alternativeCompensatedCorrections_abs_le_exact_prefix_add_running_error`, `alternativeCompensatedCorrections_partialSums_abs_sum_le_exact_prefixes_plus_self`, `alternativeCompensatedCorrectionRunningErrorBudget_of_exact_prefix_budget`, `alternativeCompensatedCorrectionExactPrefixes_abs_sum_le_five_ninth_n_sq_u`, `alternativeCompensatedCorrectionExactPrefixes_abs_sum_le_nine_tenths_n_sq_u`, `alternativeCompensatedCorrectionRunningErrorBudget_of_exact_steps`, `fl_alternativeCompensatedSum`, `alternativeCompensatedTrace_main_add_residual_le_unit_roundoff`, `alternativeCompensatedCorrections_abs_sum_le_unit_roundoff_partialSums`, `alternativeCompensatedCorrections_abs_sum_le_unit_roundoff_global_gamma`, `fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_transfer`, `fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_abs_sum_le`, `fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_running_error_budget`, `fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_running_error_budget_cap`, `fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_running_error_higham_cap`, `fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_higham_cap`, `alternativeCompensatedCorrectionRunningErrorBudget_of_pointwise_partialSums`, `fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_pointwise_correction_partial_higham_cap`, `fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_global_gamma`, `fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_global_gamma_cap`, and `not_forall_alternativeCompensated_globalGammaRadius_le_two_u_add_n_sq_u_sq_of_nu_le_tenth`. The exact-prefix lemmas identify stored correction prefixes with ordinary recursive-summation forward errors, and the computed-partial split bounds each correction-list partial by that exact prefix plus the running error from previously summed corrections. Summing those prefix bounds and absorbing the recursive correction-summing self term under `n*u<=0.1` proves the source-weighted aggregate budget `u*sum_i |partial_corrections_i| <= n^2*u^2*sum_i |x_i|`, which instantiates the running-error bridge and closes the printed `|mu_i| <= 2*u+n^2*u^2` cap. The global-gamma theorem remains as a separate source-radius route, and the route-audit theorem shows why that route alone is too weak for the exact printed cap; the pointwise bridge records an optional sufficient condition for the same aggregate budget. |
| Kahan modified no-guard correction trace | Higham §4.3, pp. 94--95 | `kahanSameSign`, `KahanModifiedNoGuardStepTrace`, `kahanModifiedNoGuardStepTrace`, `kahanModifiedNoGuardStepTrace_f`, `kahanModifiedNoGuardStepTrace_e`, `kahanModifiedNoGuardPrefixState`, `kahanModifiedNoGuardTrace`, `fl_kahanModifiedNoGuardState`, `fl_kahanModifiedNoGuardSum`, `fl_kahanModifiedNoGuardCorrection` |
| Priest doubly compensated summation trace | Higham §4.4, Algorithm 4.3 | `priestSortedByDecreasingAbs`, `priestStrictlySortedByDecreasingAbs`, `priestSortedByDecreasingAbs_of_strict`, `PriestState`, `PriestStepTrace`, `priestStepTrace`, `priestStepTrace_c`, `priestPrefixState`, `priestTrace`, `fl_priestState`, `fl_priestSum`, `fl_priestCorrection` |
| Pairwise summation | Higham §4.2, §4.6 | `fl_pairwiseSum`, `pairwiseSum_backward_error`, `pairwiseSum_forward_error_bound`, `pairwiseSum_forward_error_bound_oneSigned`, `pairwiseSum_relError_le_gamma_of_oneSigned`, `pairwiseSixTree`, `fl_pairwiseSumSixDisplayed`, `fl_pairwiseSumSixDisplayed_eq`, `pairwiseSumSixDisplayed_backward_error`, `pairwiseSumSixDisplayed_forward_error_bound`, `pairwiseCarryTree`, `fl_pairwiseCarrySum`, `pairwiseCarrySum_backward_error`, `pairwiseCarrySum_forward_error_bound`, `pairwiseCarrySum_forward_error_bound_oneSigned`, `pairwiseCarrySum_relError_le_gamma_of_oneSigned`, `fl_clog2PairwiseSum`, `clog2PairwiseSum_backward_error`, `clog2PairwiseSum_forward_error_bound`, `clog2PairwiseSum_forward_error_bound_oneSigned`, `clog2PairwiseSum_relError_le_gamma_of_oneSigned` |
| Tree summation | Higham §4.2, §4.6 | `SumTree.eval`, `SumTree.exactSum`, `SumTree.numAdds_eq`, `SumTree.backward_error`, `SumTree.forward_error`, `SumTree.forward_error_oneSigned`, `SumTree.relError_le_gamma_of_oneSigned`, `SumTree.running_error_sum_bound_from_inverse_models`, `SumTree.backward_error_n_minus_one`, `SumTree.forward_error_n_minus_one`, `SumTree.forward_error_n_minus_one_oneSigned`, `SumTree.relError_le_gamma_n_minus_one_of_oneSigned` |
| Back substitution | Higham §8.1 | `backSub_backward_error` (Theorem 8.5) |
| Forward substitution | Higham §8.1 | `forwardSub_backward_error` (Theorem 8.5) |
| Combined LU solve | Higham §8.1 | `lu_solve_combined_backward_error` (Corollary 8.6) |
| Forward error bounds | Higham §8.2 | `diag_dominant_forward_error` (Th. 8.7), `theorem_8_9` |
| M-matrix solutions | Higham §8.2 | `mmatrix_forwardSub_relative_error` (componentwise relative error in μ-form) |
| Inverse bounds | Higham §8.3 | `abs_inv_le_compMatrix_inv`, `triInv_row_sum_upperBound`, `triInv_infNorm_upperBound`, `triInv_infNorm_sq_budget_of_diagDominantUpper`, `triInv_infNorm_sq_budget_of_diagDominantUpper_det_ne_zero` (Th. 8.11, 8.13) |
| LU factorization | Higham §9.3 | `LUBackwardError` (Theorem 9.3) |
| LU solve | Higham §9.4 | `lu_solve_backward_error` (Theorem 9.4) |
| SPD matrices | Higham §9.4 | `spd_growth_factor_bound`, `spd_backward_stability` (Th. 9.11) |
| M-matrix LU | Higham §9.4 | `mmatrix_optimal_growth` (Theorem 9.11) |
| Banded LU | Higham §9.5 | `banded_lu_backward_error` |

## Installation

Add to your `lakefile.toml`:

```toml
[[require]]
name = "LeanFpAnalysis"
git = "https://github.com/AlexGeorgantzas/lean-fp-analysis"
rev = "main"
```

Or to your `lakefile.lean`:

```lean
require LeanFpAnalysis from git
  "https://github.com/AlexGeorgantzas/lean-fp-analysis" @ "main"
```

Then in your Lean files:

```lean
import LeanFpAnalysis.FP
```

## Building

Requires [Lean 4](https://leanprover.github.io) with [Lake](https://github.com/leanprover/lean4/tree/master/src/lake).

```bash
lake build
```

- Lean toolchain: `leanprover/lean4:v4.29.0-rc3`
- Mathlib: `v4.29.0`

> **Note:** On a fresh clone, `lake build` may fail with a ProofWidgets build error. Run:
> ```bash
> curl -L https://github.com/leanprover-community/ProofWidgets4/releases/download/v0.0.90/ProofWidgets4.tar.gz \
>   -o /tmp/pw.tar.gz
> mkdir -p .lake/build/packages/proofwidgets
> tar xzf /tmp/pw.tar.gz -C .lake/build/packages/proofwidgets
> ```

## Usage example

```lean
import LeanFpAnalysis.FP
open LeanFpAnalysis.FP

variable (fp : FPModel) (n : ℕ)

-- The γ-function bounds accumulated rounding error
#check gamma fp n  -- γ(n) = nu / (1 - nu)

-- Dot product: |fl(x·y) - x·y| ≤ γ(n) · Σ|xᵢ||yᵢ|
#check dotProduct_error_bound

-- Back substitution: (U + ΔU)x̂ = b with |ΔU| ≤ γ(n)|U|
#check backSub_backward_error

-- LU solve: (A + ΔA)x̂ = b with |ΔA| ≤ (3γ(n) + γ(n)²)|L̂||Û|
#check lu_solve_backward_error
```

## RandNLA Algorithm 1

The RandNLA development formalizes Algorithm 1 from Petros Drineas and
Michael W. Mahoney, ["RandNLA: Randomized Numerical Linear Algebra"](https://dl.acm.org/doi/10.1145/2842602),
Communications of the ACM 59(6), 80-90, 2016. It uses element-wise sampling
with squared-magnitude probabilities

```
p_ij = A_ij^2 / sum_{k,l} A_kl^2.
```

By current project convention, these sampling probabilities are exact
mathematical inputs to the sampler. The floating-point Algorithm 1 theorems
therefore charge sampled-entry rescaling, accumulation, and residual arithmetic,
but they do not model probability construction, normalization repair,
cumulative/alias sampling, or a sampling-law perturbation term.

The deterministic theorem family reduces the floating-point trace error to a bound on the hit counter `q_ij`. The randomized theorem family then proves high-probability hit-count bounds using finite Markov, pairwise-Chebyshev, and Chernoff arguments.
The exact trace law also proves support-inclusive unbiasedness of the sampled
matrix estimator under the canonical independent squared-magnitude sampler.
For future spectral concentration work, the exact residual is now also exposed
as a sum of one-sample mean-zero residual increments under the same law. The
same module proves entrywise, Frobenius, and fixed-vector second-moment bounds
for these increments, plus fixed-vector and finite-test-set Markov tails for
the full residual in exact and floating-point arithmetic. A covering-net
support theorem now upgrades finite vector tests plus a Frobenius residual
event into exact and floating-point rectangular operator events under an
explicit finite unit-ball-cover assumption. The shared matrix algebra layer
now also proves a product-grid cover reduction: a one-dimensional grid for
`[-1,1]` at radius `delta` yields an `n`-dimensional unit-ball cover at radius
`sqrt n * delta`, with index cardinality `|grid|^n`. This remains a
Markov/cover support route, not the CACM equation (2) matrix
Bernstein/Khintchine theorem. The
matrix-concentration route has also gained a self-adjoint dilation bridge:
future square-matrix tail bounds for the dilation now transfer to exact and
floating-point rectangular residual events, and the one-step dilation
increments are proved mean-zero with an explicit squared-Frobenius proxy. The
shared matrix algebra layer also has finite square product/trace vocabulary,
basic trace algebra, finite-index PSD/Loewner-order vocabulary, finite-index
quadratic-form control from `finiteOpNorm2Le`, and the trace-of-square identity
for the dilation, `tr(D(M)^2) = 2 ||M||_F^2`. The Algorithm 1 spectral file now
also proves the quadratic-form, Loewner-order, and PSD variance proxies for the
squared dilation increments and their `s`-step summed versions, giving the
local variance-parameter shape needed before a trace-exponential or matrix
Bernstein theorem can be formalized. The same one-step variance and zero-mean
facts are now lifted through the independent product trace law: the full
self-adjoint dilation residual is entrywise mean-zero, and the trace-law
expectation of the summed squared dilation increments has the same
quadratic-form, Loewner, and PSD variance bounds. The same product-law layer
also proves a generic scalar exponential-moment factorization for any one-step
statistic `f`: the MGF of `sum_t f(X_t)` is exactly the `s`th power of the
one-step MGF, with exponential-Markov upper-tail and complement forms. This
scalar MGF layer now also has a finite-family union-bound form and a
self-adjoint-dilation quadratic-form specialization, so supplied finite test
families can be controlled from one-step scalar MGF hypotheses, or from
pointwise one-step bounds via a fully proved local MGF adapter. The MGF layer
also has support-aware pointwise variants: a one-step bound only has to hold on
positive-probability samples, which avoids hidden retained-entry assumptions in
the truncated law. This is
infrastructure for future cover or trace-exponential routes, not a matrix
Bernstein theorem. It also has deterministic adapters from a one-sided dilation
Loewner event `D(R) <= eps I`, from its eigenvalue restatement
`lambda(eps I - D(R)) >= 0`, and from a squared dilation Loewner event
`D(R)^2 <= eps^2 I` to the exact and floating-point rectangular spectral events,
plus a finite union-bound adapter that combines supplied single-eigenvalue
probability bounds into that eigenvalue event. Thus a future largest-eigenvalue
or squared-moment concentration theorem can target those events without hiding
the conversion step. The matrix algebra
layer now also converts local finite symmetry/PSD/Loewner predicates to
mathlib's `Matrix.IsSymm`/`Matrix.PosSemidef` vocabulary, so that future
spectral or matrix-exponential arguments can reuse mathlib without changing
the RandNLA algorithm statements. The spectral bridge now also exposes the
repository-native matrix exponential and proves the scalar-identity trace
normalization `tr(exp(L I)) = d exp(L)`, the normalization term needed by a
future trace-exponential concentration proof; it also preserves the local
symmetry predicate through matrix exponentiation, proves the diagonal identity
`tr(exp(diag v)) = sum_i exp(v_i)`, exposes a Hermitian CFC exponential
whose trace is exactly `sum_i exp(lambda_i(M))`, and now proves the same trace
diagonalization for the repository-native power-series `finiteMatrixExp` for
local finite real symmetric matrices, together with the lower-tail identity
`tr(exp(-M)) = sum_i exp(-lambda_i(M))`. A new matrix-concentration bridge
proves the deterministic witnesses `exp(T) <= tr(exp(M))` when some Hermitian
eigenvalue of `M` is at least `T`, and `exp(-T) <= tr(exp(-M))` when some
Hermitian eigenvalue is at most `T`; it then derives the corresponding
finite-probability exponential-Markov trace tails, scalar-bound variants, and
high-probability complements where all Hermitian eigenvalues stay below or
above the threshold. This still leaves the trace-exponential expectation bound
itself open. The analysis layer also records mathlib's operator-log
monotonicity for complex `CStarMatrix` as `cstarMatrix_log_le_log`, one of the
functional-calculus dependencies used by the Tropp/Lieb trace-MGF route.
`OperatorLog` also exposes the finite-dimensional `CStarMatrix` topological
and real-functional-calculus bridges needed by the normed-algebra exponential,
and proves `log(exp X) = X` for self-adjoint matrices in normed-space, complex
CFC, and real CFC exponential forms. It also exposes the matching
nonnegative-spectrum bridge needed by mathlib's `CFC.exp_log` and proves
`exp(log A) = A` for strictly positive complex `CStarMatrix` objects in
normed-space, complex CFC, and real CFC exponential forms. These are
deterministic analytic dependencies; the LiebTrace layer now composes them into
the finite-dimensional Lieb theorem. The
companion `CStarMatrixBridge` layer embeds repository finite real matrices into
complex `CStarMatrix`, preserves subtraction, the identity, scalar identities,
and self-adjointness for symmetric matrices, and carries local finite PSD and
Loewner inequalities into the complex C⋆ spectral order. The same bridge now
proves strict positivity after adding a positive scalar identity
regularization. It also contains the block algebra needed by the
Hansen--Pedersen route: the block diagonal `cstarMatrixBlockDiagonal`, the
vertical block column `cstarMatrixColumnPair`, the identities
`cstarMatrixColumnPair_conjTranspose_mul_self`,
`cstarMatrixBlockDiagonal_mul_columnPair`, and
`cstarMatrixColumnPair_conjTranspose_mul_blockDiagonal_mul_columnPair`, plus the
isometry normalization
`cstarMatrixColumnPair_conjTranspose_mul_self_eq_one_of_sum`. It also proves
the range-projection algebra for \(V=[A;B]\): `cstarMatrixColumnPairRangeProjection`,
`cstarMatrixColumnPairRangeProjection_isSelfAdjoint`,
`cstarMatrixColumnPairRangeProjection_mul_self_of_sum`,
`cstarMatrixColumnPairRangeProjection_mul_columnPair_of_sum`, and
`cstarMatrixColumnPair_conjTranspose_mul_rangeProjection_of_sum`. The same
layer now defines the projection reflection \(2P-I\) and proves that it is
self-adjoint when \(P\) is self-adjoint, squares to the identity when \(P^2=P\),
is a unitary unit, and fixes \(V\) when \(PV=V\), via
`cstarMatrixProjectionReflection_mul_self_of_idempotent`,
`cstarMatrixProjectionReflection_isUnit_of_idempotent`,
`cstarMatrixProjectionReflection_mem_unitary_of_isSelfAdjoint_of_idempotent`, and
`cstarMatrixColumnPairRangeReflection_mul_columnPair_of_sum`. It also proves the
right-absorption companion
`cstarMatrixColumnPair_conjTranspose_mul_rangeReflection_of_sum` and the
pinching-average compression identity
`cstarMatrixColumnPair_reflectionAverage_compression_of_sum`, saying that
compressing \((D+RDR)/2\) by the block isometry gives the same result as
compressing \(D\) whenever \(R=2VV^*-I\) and \(V^*V=I\). The same algebraic
pinching layer proves `cstarMatrixColumnPair_reflectionAverage_conj_rangeReflection_of_sum`
and `cstarMatrixColumnPair_reflectionAverage_commute_rangeReflection_of_sum`,
so the averaged block is invariant under, and commutes with, the range
reflection. It also proves
`cstarMatrixColumnPair_reflectionAverage_commute_rangeProjection_of_sum`, so the
averaged block commutes with the range projection \(VV^*\). The range-reduction
identities
`cstarMatrixColumnPair_reflectionAverage_mul_columnPair_of_sum` and
`cstarMatrixColumnPair_conjTranspose_mul_reflectionAverage_of_sum` further show
that the averaged block acts on \(V\) and \(V^*\) through the same compressed
corner \(V^*DV\) as the original block \(D\). The block
diagonal constructor is also now proved to preserve zero, identity, additive
structure, star, multiplication, units, nonnegativity, and strict positivity
through lemmas such as `cstarMatrixBlockDiagonal_star`,
`cstarMatrixBlockDiagonal_mul`, `cstarMatrixBlockDiagonal_nonneg`, and
`cstarMatrixBlockDiagonal_isStrictlyPositive`; the bundled homomorphism
`cstarMatrixBlockDiagonalStarAlgHom` is continuous. The CFC lemma
`cstarMatrixBlockDiagonal_cfc` then proves
\(f(\operatorname{diag}(T_1,T_2))=\operatorname{diag}(f(T_1),f(T_2))\) for
self-adjoint blocks and functions continuous on the union of the two spectra.
The CFC conjugation lemma `cstarMatrix_cfc_unitary_conj` also proves
\(f(UTU^*) = U f(T) U^*\) for unitary \(U\) and self-adjoint \(T\), while
`cstarMatrix_unitary_conj_isStrictlyPositive` and
`cstarMatrixColumnPairRangeReflection_conj_isStrictlyPositive_of_sum` record
that unitary conjugation, in particular by the range reflection, preserves
strict positivity. The order lemmas `cstarMatrix_compression_nonneg` and
`cstarMatrix_compression_mono` show that rectangular C⋆-matrix compression
preserves nonnegativity and order. Combining ordinary all-finite operator
convexity with the range-reflection CFC identity now gives the pinching
inequality
`cstarMatrixColumnPair_reflectionAverage_cfc_le_average_of_sum`, and compressing
it gives `cstarMatrixColumnPair_reflectionAverage_compressed_cfc_le_compressed_of_sum`.
This closes the CFC pinching-inequality side of the Hansen--Pedersen block
route. The shifted-inverse kernel corner is also closed:
`cstarMatrix_units_inv_mul_rect_eq_mul_units_inv_of_mul_eq` proves the
rectangular algebra \(UV=VW \Rightarrow U^{-1}V=VW^{-1}\),
`cstarMatrix_cfc_shifted_inv_mul_rect_eq_mul_cfc_shifted_inv_of_mul_eq` lifts
this to \(x\mapsto(s+x)^{-1}\), and
`cstarMatrixColumnPair_reflectionAverage_shifted_inv_corner_of_sum` specializes
it to \(V^*(sI+(D+RDR)/2)^{-1}V=(sI+V^*DV)^{-1}\). The full
\(x\log x\) corner is also closed by
`cstarMatrixColumnPair_reflectionAverage_xlog_corner_of_sum`, and the concrete
two-point Hansen--Pedersen theorem is closed by
`cstarMatrixXLogXHansenPedersenJensenTarget_of_unit_interval_kernel`.
The affine-corrected entropy kernel \(x\log x-(x-1)\), which is the scalar
kernel for normalized matrix-relative-entropy perspectives, now has both
ordinary all-finite-size operator convexity
`cstarMatrixEntropyKernelPositiveOperatorConvexAllFiniteTarget_of_unit_interval_kernel`
and two-point Jensen
`cstarMatrixEntropyKernelHansenPedersenJensenTarget_of_unit_interval_kernel`.
The same route now also has the square-root substrate needed before forming
finite perspective objects: `cstarMatrixPositiveSqrt`,
`cstarMatrixPositiveInvSqrt`, `cstarMatrixPositiveSqrt_mul_self`,
`cstarMatrixPositiveInvSqrt_mul_sqrt`,
`cstarMatrixPositiveSqrt_mul_invSqrt`,
`cstarMatrixPositiveInvSqrt_isUnit`,
`cstarMatrixPositiveInvSqrt_mul_self_mul`, and
`cstarMatrixPositiveInvSqrt_conj_isStrictlyPositive`. These formalize
\(A^{1/2}\), \(A^{-1/2}\), the inverse identities and
\(A^{-1/2}AA^{-1/2}=I\), plus strict-positivity preservation under
inverse-square-root congruence. They are perspective substrate only, not yet
Effros's superoperator trace representation of relative entropy.
The ordinary finite perspective theorem for the normalized entropy kernel is
also now local: `cstarMatrixPerspective` and
`cstarMatrixEntropyKernelPerspective_jointConvex` prove joint convexity of
\(P_f(X,A)=A^{1/2}f(A^{-1/2}XA^{-1/2})A^{1/2}\) for
\(f(x)=x\log x-(x-1)\). This is still not the source-faithful superoperator
trace representation of Umegaki relative entropy, so it does not close
`cstarMatrixRelativeEntropyJointConvexOnStrictPositive`.
The source-faithful trace-representation target
`cstarMatrixRelativeEntropyTraceRepresentationBySuperoperator` is now closed by
`cstarMatrixRelativeEntropyTraceRepresentationBySuperoperator_all`, using the
relative modular operator \(L_XR_A^{-1}\) rather than the ordinary source-matrix
perspective. The proof factors the finite-matrix expression through
`matrixSuperoperatorEntropyKernelTrace`, proves the limiting overlap expansion
`matrixSuperoperatorEntropyKernelOverlapExpansion_all`, and then applies
`matrixRelativeEntropyTraceRepresentation_of_superoperator_overlap` to match
the compact relative-entropy trace side closed by
`matrixTrace_hermitianCfc_relativeEntropy_re_eq_sum`. The remaining
source-theorem blocker is joint convexity of this source-faithful
relative-entropy representation, not the trace representation itself.
The next layer closes the product-index superoperator lifts
`cstarMatrixSuperoperatorLeftLift` and `cstarMatrixSuperoperatorRightLift`,
their affine/strict-positivity lemmas, and quadratic-form monotonicity
`matrixComplexQuadraticForm_re_mono_of_cstarMatrix_le`. The ordinary
product-index perspective trace is now packaged as
`cstarMatrixSuperoperatorPerspectiveTrace` and proved jointly convex by
`cstarMatrixSuperoperatorPerspectiveTrace_jointConvex`. The
reduction
`cstarMatrixRelativeEntropyJointConvexOnStrictPositive_of_perspectiveTraceRepresentation`
shows why the equality bridge is sufficient, and that bridge is now closed by
`cstarMatrixSuperoperatorPerspectiveTrace_eq_matrixSuperoperatorEntropyKernelTrace`
and `cstarMatrixRelativeEntropyPerspectiveTraceRepresentation_all`. The
equality-bridge algebra includes
`cstarMatrixSuperoperatorLeftLift_rightLift_commute`,
`cstarMatrixSuperoperatorPositiveInvSqrtRightLift_commute_leftLift`, and
`cstarMatrixSuperoperatorPerspective_normalizedArgument_reorder`, which prove
the lift commutation and normalized-argument reorder used by the final
CFC square-root identification. The generic square-root identity
`cstarMatrixPositiveInvSqrt_mul_self_eq_unit_inv` and its right-lift
combination
`cstarMatrixSuperoperatorPerspective_normalizedArgument_eq_leftLift_mul_rightLift_unit_inv`
put the normalized argument in the \(L_XR_A^{-1}\) shape.
The outer square-root commutation dependency is also local:
`cstarMatrixPositiveSqrt_commute_unit_inv`,
`cstarMatrixSuperoperatorPositiveSqrtRightLift_commute_leftLift`, and
`cstarMatrixSuperoperatorLeftLift_mul_rightLift_unit_inv_commute_positiveSqrtRightLift`
prove that \(L_XR_A^{-1}\) commutes with \(R_A^{1/2}\).
The same source route also has
the compression-domain
lemmas `cstarMatrixColumnPair_mulVec_injective_of_sum`,
`cstarMatrixColumnPair_compress_blockDiagonal_isStrictlyPositive_of_sum`, and
`cstarMatrixHansenPedersenCompression_isStrictlyPositive_of_sum`, proving that
the block-isometry compression \(V^* \operatorname{diag}(T_1,T_2)V\), hence
\(A^*T_1A+B^*T_2B\), is strictly positive when \(T_1,T_2\) are strictly
positive and \(A^*A+B^*B=I\).
These close the `[A;B]`/`diag(T1,T2)` algebraic, range-projection/reflection,
pinching-average compression/invariance/projection-commutation/range-reduction, order-theoretic, block-diagonal CFC,
unitary-conjugation CFC/positivity, CFC pinching inequality, shifted-inverse
corner subcase, full \(x\log x\) corner assembly, and concrete compression/Jensen
inequality. The later Algorithm 1 source route now closes the iterated
trace-MGF / matrix Bernstein layer for the cited square theorem; these
operator-convexity results remain reusable foundations.
`OperatorLog` turns a local
finite Loewner inequality into a regularized operator-log inequality. A small
`CStarMatrixTrace` layer defines
the complex C-star trace, proves add/subtract/scalar/cyclic trace algebra,
shows trace real-part positivity and monotonicity for the C-star spectral
order, proves that the trace of a self-adjoint complex C-star matrix is
real-valued, agrees with the repository's `finiteTrace` after finite-real
embedding, and specializes PSD/Loewner trace nonnegativity and monotonicity to
embedded finite real matrices. It also exposes the finite-real embedding as a
continuous ring homomorphism, proves that this embedding commutes with the
repository-native finite real matrix exponential, and gives the trace bridge
`Re tr(exp(embed M)) = finiteTrace(finiteMatrixExp M)`. It also proves the
scalar CFC-exponential trace normalization `tr(exp(aI)) = exp(a) d` for
complex C-star matrices. The
`CStarMatrixExpectation`
layer adds finite-probability expectation for complex scalars and entrywise
complex C-star-matrix-valued random variables, proves complex linearity,
commutation of trace with expectation, compatibility with finite-real
embedding, real and complex weighted-sum forms, preservation of C-star
nonnegativity/monotonicity, and strict positivity after positive
scalar-identity regularization. The finite probability layer also exposes a
Jensen wrapper for concave real-valued functions, and the C-star expectation
layer specializes it to C-star-matrix random variables. It now also includes a
generic Chernoff optimizer:
`FiniteProbability.eventProb_real_le_mean_add_ge_one_sub_exp_sq_of_subgaussian_mgf`
turns a centered subgaussian MGF estimate into the one-sided
`exp(-t^2/(2 sigma^2))` high-probability tail. This is the reusable
MGF-to-tail step for the future Ledoux/Talagrand convex-Lipschitz Rademacher
foundation. The same file now also records the finite MGF/Herbst calculus
substrate `FiniteProbability.expectationReal_exp_pos`,
`FiniteProbability.hasDerivAt_expectationReal_exp_mul`,
`FiniteProbability.hasDerivAt_log_expectationReal_exp_mul`,
`FiniteProbability.entropyReal`, and
`FiniteProbability.entropyReal_exp_mul_eq`. The same module now also defines
the unbiased Bernoulli coordinate law `FiniteProbability.boolUniformProbability`
and proves its point-mass, expectation, and entropy formulas
`FiniteProbability.boolUniformProbability_prob`,
`FiniteProbability.boolUniformProbability_expectationReal`, and
`FiniteProbability.entropyReal_boolUniformProbability_eq`, plus the scalar
two-point entropy bound `FiniteProbability.twoPointEntropy_le_sq_sub_div_of_pos`
and positive-function Bernoulli coordinate log-Sobolev inequality
`FiniteProbability.entropyReal_boolUniformProbability_sq_le_sq_sub_of_pos`.
The probability layer also proves the finite `L2` norm bridge
`FiniteProbability.abs_sqrt_expectationReal_sq_sub_le_sqrt_expectationReal_sub_sq`
and its Bernoulli-coordinate specialization
`FiniteProbability.boolUniformProbability_abs_sqrt_expectationReal_sq_sub_le_sqrt_expectationReal_sub_sq`,
which supply the section-norm reverse-triangle step needed by the remaining
finite-cube tensorization induction.
The same Ledoux route now has the one-coordinate product peel-off
`FiniteProbability.entropyReal_prod_boolUniformProbability_sq_le_coordinate_add_entropy`,
which bounds the entropy of `g^2` on `P x Bool` by the Bernoulli-coordinate
squared difference plus the entropy of the conditional second moment. Together
with the `L2` section-norm bridge, the abstract induction lift
`FiniteProbability.entropyReal_prod_boolUniformProbability_sq_le_lifted_diff_sum_add`
now carries an existing entropy-gradient bound on `P` to `P x Bool`.
`Preconditioning.lean` instantiates that lift on the concrete
`RademacherTrace m` cube in
`rademacherTraceProbability_entropyReal_sq_le_sum_flip`, proving the finite
cube entropy-gradient inequality for Boolean coordinate flips. It also proves
flip invariance of the uniform Rademacher law and scalar/symmetrized
exponential-tilt bridges:
`rademacherTraceProbability_expectationReal_flip`,
`real_exp_half_sub_sq_le_two_mul_half_diff_sq`,
`rademacherTraceProbability_flip_tilt_sq_sum_bound_of_pointwise_halfdiff_sq_le`,
and `rademacherTraceProbability_flip_tilt_sq_sum_bound_of_pointwise_absdiff_le`.
These close the scalar and finite-cube symmetrization dependencies for the
tilt route.  The later positive-drop self-bounding branch closes the
source-sharp signed-Hadamard row-norm theorem used by the SRHT route; the
general Ledoux/Talagrand convex-Lipschitz theorem remains advisory rather than
an open Algorithm 3 dependency.
It also proves
the conditional exponential-tilt reduction
`rademacherTraceProbability_entropyReal_exp_mul_le_of_flip_tilt_sq_sum_bound`
and the corresponding conditional Chernoff wrapper
`rademacherTraceProbability_eventProb_real_le_mean_add_ge_one_sub_exp_sq_of_flip_tilt_sq_sum_bound`.
These theorems expose a deterministic flip-gradient estimate for
`exp (lam * X / 2)` as the reusable interface.  In the signed-Hadamard row-norm
case that interface is discharged by the positive-drop self-bounding theorem,
so the SRHT row-norm bound is now local even though the fully general
Ledoux/Talagrand convex-Lipschitz proposition is not formalized.
The finite
product-law layer now also proves `FiniteProbability.prod_expectationReal_eq`,
`FiniteProbability.prod_expectationReal_fst_eq`, and
`FiniteProbability.entropyReal_prod_eq_expectation_entropyReal_add_entropyReal_expectation`,
the exact entropy chain rule used as a tensorization dependency on the Ledoux
route. It also proves
`FiniteProbability.log_mgf_differential_le_of_entropyReal_exp_mul_le`,
`FiniteProbability.log_mgf_div_sub_quadratic_antitoneOn_of_differential_le`,
`FiniteProbability.tendsto_log_mgf_div_nhdsGT_zero`,
`FiniteProbability.log_mgf_le_mean_add_quadratic_of_differential_le`,
`FiniteProbability.log_mgf_le_mean_add_quadratic_of_entropyReal_exp_mul_le`,
`FiniteProbability.expectationReal_exp_centered_le_exp_of_log_mgf_le`, and
`FiniteProbability.eventProb_real_le_mean_add_ge_one_sub_exp_sq_of_log_mgf_bound`,
plus
`FiniteProbability.eventProb_real_le_mean_add_ge_one_sub_exp_sq_of_entropyReal_exp_mul_le`.
These lemmas provide exponential moment positivity, MGF/log-MGF derivatives,
entropy-of-exponential algebra, entropy-bound-to-differential conversion, and
the finite Herbst extraction from corrected-log-MGF quotient monotonicity and
the right-limit at zero to the log-Laplace bound, plus log-Laplace-to-tail
conversion and the final entropy-bound-to-tail composition; they do not
themselves prove the convex concentration theorem. The
`LiebTrace` layer now
names the strictly positive complex `CStarMatrix` cone, proves that it is
convex over real scalars, records the scalar positivity lemmas needed for that
domain, names the local functional `A ↦ Re tr(exp(H + log A))`, and proves the local trace-exponential nonnegativity,
trace real-valuedness, and functional nonnegativity wrappers for self-adjoint
`H`. It also identifies the local CFC definition with the standard
normed-algebra exponential form used in Tropp-style trace-MGF statements and
normalizes the `H = 0` case to `Re tr(A)` on the strictly positive cone. This
also proves the affine `H = 0` special case of the local Lieb concavity target.
It also proves the conditional one-step Tropp/Jensen trace-MGF adapter and the
unconditional wrapper `FiniteProbability.expectationReal_trace_normed_exp_add_le`:
finite self-adjoint matrix random variables satisfy
`E Re tr exp(H + X) <= Re tr exp(H + log (E exp X))`.
For the chosen Tropp relative-entropy route to Lieb, it also proves scalar
and finite-vector relative-entropy nonnegativity
(`realRelativeEntropy_nonneg`, `finiteRealRelativeEntropy_nonneg`), the finite
log-sum inequality (`finite_log_sum_inequality`), and scalar/finite-vector
joint convexity of the commutative relative entropy
(`realRelativeEntropy_jointConvex`,
`finiteRealRelativeEntropy_jointConvex`). It names
`cstarMatrixRelativeEntropy` and proves the diagonal normalization
`cstarMatrixRelativeEntropy_self`. It also builds a diagonal star-algebra/log
bridge (`cstarMatrixDiagonalStarAlgHom`, `cstarMatrix_log_realDiagonal`) and
proves that real diagonal C-star matrix relative entropy reduces to finite
vector relative entropy, hence is nonnegative and jointly convex for positive
diagonal entries
(`cstarMatrixRelativeEntropy_realDiagonal`,
`cstarMatrixRelativeEntropy_realDiagonal_nonneg`,
`cstarMatrixRelativeEntropy_realDiagonal_jointConvex`). In addition it proves the
real scalar-identity reduction and nonnegativity sanity check
(`cstarMatrixRelativeEntropy_algebraMap_real`,
`cstarMatrixRelativeEntropy_algebraMap_real_nonneg`).
For the front-loaded Hansen--Pedersen/Effros proof route, it now also names
the ordinary positive-cone operator-convexity source target
`cstarMatrixPositiveOperatorConvexTarget`, the all-finite-size source target
`cstarMatrixPositiveOperatorConvexAllFiniteTarget`, proves the identity-function
sanity cases `cstarMatrixPositiveOperatorConvexTarget_id` and
`cstarMatrixPositiveOperatorConvexAllFiniteTarget_id`, names both the fixed-size
and all-finite-size Hansen--Pedersen transfer targets
`cstarMatrixPositiveHansenPedersenTransferTarget` and
`cstarMatrixPositiveHansenPedersenTransferAllFiniteTarget`, and records the
concrete `x log x` source split
`cstarMatrixXLogXPositiveOperatorConvexTarget` /
`cstarMatrixXLogXHansenPedersenTransferTarget` plus the source-faithful
all-finite targets `cstarMatrixXLogXPositiveOperatorConvexAllFiniteTarget` and
`cstarMatrixXLogXHansenPedersenTransferAllFiniteTarget`. It also keeps the
assembled two-point operator Jensen source target
`cstarMatrixHansenPedersenJensenTwoPointTarget`, proves the identity-function
sanity case `cstarMatrixHansenPedersenJensenTwoPointTarget_id`, and records
the concrete `x log x` positive-cone target
`cstarMatrixXLogXHansenPedersenJensenTarget`. The assembly adapter
`cstarMatrixXLogXHansenPedersenJensenTarget_of_positiveOperatorConvex_of_transfer`
records the generic source split. The concrete `x log x` target is now closed
without a hidden transfer assumption by the reflection-average proof
`cstarMatrixXLogXHansenPedersenJensenTarget_of_reflectionAverage_xlog_corner`,
packaged as
`cstarMatrixXLogXHansenPedersenJensenTarget_of_unit_interval_kernel`. The
normalized entropy-kernel target follows from it by
`cstarMatrixEntropyKernelPositiveOperatorConvexTarget_of_unit_interval_kernel`
and
`cstarMatrixEntropyKernelHansenPedersenJensenTarget_of_unit_interval_kernel`.
It also closes the CFC square-root and inverse-square-root identities needed to
state the next perspective layer without hidden algebraic hypotheses:
`cstarMatrixPositiveSqrt_mul_self`,
`cstarMatrixPositiveInvSqrt_mul_sqrt`,
`cstarMatrixPositiveSqrt_mul_invSqrt`,
`cstarMatrixPositiveInvSqrt_isUnit`,
`cstarMatrixPositiveInvSqrt_mul_self_mul`, and
`cstarMatrixPositiveInvSqrt_conj_isStrictlyPositive`.
The older
transfer-only bridges remain as diagnostics for the generic
Hansen--Pedersen/Effros route, but the concrete two-point Jensen theorem is no
longer an open blocker. For the Bendat--Sherman alternate route, it
also proves the derivative-monotonicity subdependency
`cstarMatrixXLogXDerivativeMonotoneTarget_of_log_monotone`, using the local
operator-log monotonicity wrapper and the CFC normalization
`cstarMatrix_cfc_one_add_log_eq_one_add_log`. The exact remaining bridge is
now more source-faithfully named through divided differences as
`realXLogXDividedDifference`,
`realXLogXDividedDifference_self`,
`realXLogXDividedDifference_eq_log_add_ratio`,
`realXLogXDividedDifference_eq_log_add_normalized`,
`realNormalizedLogKernel`,
`realNormalizedLogKernel_eq_mul_dslope_log`,
`continuousOn_realNormalizedLogKernel_Ioi`,
`realXLogXDividedDifference_eq_log_add_normalizedKernel`,
`real_normalizedLogKernel_offdiag_intervalIntegral`,
`realNormalizedLogKernel_setIntegral`,
`real_xlog_eq_sub_one_mul_realNormalizedLogKernel`,
`real_xlog_eq_sub_one_mul_normalizedKernel_setIntegral`,
`real_xlog_eq_unit_interval_xlog_kernel_integral`,
`real_unit_interval_xlog_integrand_eq_affine_add_shifted_inv`,
`real_unit_interval_xlog_kernel_integrand_eq_affine_add_shifted_inv`,
the C-star spectrum bridge `cstarMatrix_spectrum_nonneg_of_nonneg`, and the
unital inverse-kernel/fractional-kernel monotonicity lemmas
`cstarMatrix_cfc_one_sub_one_add_inv_monotone` and
`cstarMatrix_cfc_pos_over_one_add_monotone`, together with the scaled
fractional-kernel theorem `cstarMatrix_cfc_pos_over_pos_add_monotone` and the
unit-interval interior integrand theorem
`cstarMatrix_cfc_unit_interval_fractional_kernel_monotone`,
the strict-positive endpoint-inclusive version
`cstarMatrix_cfc_unit_interval_fractional_kernel_monotone_of_mem_Icc`,
and the joint-continuity side condition
`continuousOn_uncurry_unit_interval_fractional_kernel_spectrum`,
the scalar/spectral boundedness side conditions
`real_unit_interval_fractional_kernel_abs_le_max_of_le`,
`real_unit_interval_fractional_kernel_spectrum_norm_le_max`,
`ae_unit_interval_fractional_kernel_spectrum_norm_le_max`,
`hasFiniteIntegral_const_max_one_spectrum_bound`,
`continuousOn_uncurry_unit_interval_subtype_fractional_kernel_spectrum`,
`ae_unit_interval_subtype_fractional_kernel_spectrum_norm_le_max`, and
`hasFiniteIntegral_unit_interval_subtype_const_max_one_spectrum_bound`,
the CFC scalar-integral equality
`cstarMatrix_cfc_realNormalizedLogKernel_eq_unit_interval_integral`,
the matrix-order set-integral helper `cstarMatrix_setIntegral_mono_on`,
and the normalized logarithmic-kernel operator-monotonicity theorems
`cstarMatrix_cfc_realNormalizedLogKernel_monotone_of_spectrum_bound` and
`cstarMatrix_cfc_realNormalizedLogKernel_monotone`,
the base-point scaling/constant-shift CFC normalization
`cstarMatrix_cfc_realXLogXDividedDifference_eq_log_add_scaled_normalizedKernel`,
finite nonnegative-combination closure
`cstarMatrix_cfc_finset_sum_nonneg_mul_pos_over_pos_add_monotone`,
plus the generic CFC Bochner-integral order lift
`cfc_integral_mono_of_forall_of_bound`,
`cstarMatrixXLogXDividedDifferenceMonotoneTarget`, and
`cstarMatrixXLogXDividedDifferenceMonotoneTarget_of_normalizedLogKernel`, and
`cstarMatrixBendatShermanDividedDifferenceBridgeTarget`, with adapter
`cstarMatrixXLogXPositiveOperatorConvexTarget_of_bendatShermanDividedDifferenceBridge`.
The older derivative-only bridge is also recorded as
`cstarMatrixBendatShermanDerivativeBridgeTarget`, with adapter
`cstarMatrixXLogXPositiveOperatorConvexTarget_of_bendatShermanDerivativeBridge`.
As a separate source-standard route check, the finite matrix Schur-complement
dependency for direct integral-representation proofs is now closed:
`matrix_posDef_inverse_schur_block`, `matrix_weighted_inverse_schur_block`,
`matrix_posDef_weighted_sum`, and `matrix_inv_convex_posDef` prove inverse
convexity on the positive-definite finite complex matrix cone. The bridge
lemmas `cstarMatrix_nonneg_of_matrix_posSemidef` and
`cstarMatrix_le_of_matrix_le` lift plain finite-matrix Loewner inequalities
back to C-star order, and `cstarMatrix_cfc_inv_convex_isStrictlyPositive`
gives inverse-kernel convexity in the finite C-star CFC vocabulary. The direct
route now also has `cstarMatrix_cfc_shifted_inv_eq_cfc_inv_add_smul_one` and
`cstarMatrix_cfc_shifted_inv_convex_nonneg`, giving the shifted inverse-kernel
family \(x \mapsto (s+x)^{-1}\) on the nonnegative cone for \(s>0\).

The corrected direct route now closes ordinary positive-cone operator
convexity of `x ↦ x log x`. The auxiliary integrand
`(x - 1)^2 / (u + (1 - u) x)` is still available as a true scalar/CFC
decomposition, but the integrand that reconstructs `x log x` is
`x * (x - 1) / (u + (1 - u) x)`. The scalar identity and CFC lift are
`real_xlog_eq_unit_interval_xlog_kernel_integral`,
`cstarMatrix_cfc_unit_interval_xlog_kernel_integrand_eq_affine_add_shifted_inv`,
`continuousOn_uncurry_unit_interval_xlog_kernel_spectrum`,
`real_unit_interval_xlog_kernel_spectrum_norm_le_max_sq`,
`ae_unit_interval_xlog_kernel_spectrum_norm_le_max_sq`,
`hasFiniteIntegral_const_max_one_spectrum_bound_sq`, and
`cstarMatrix_cfc_xlog_eq_unit_interval_xlog_kernel_integral`. The pointwise
kernel-convexity theorems
`cstarMatrix_cfc_unit_interval_xlog_integrand_convex_of_pos_lt_one` and
`cstarMatrix_cfc_unit_interval_xlog_kernel_integrand_convex_of_pos_lt_one`
feed the final dependency closure
`cstarMatrixXLogXPositiveOperatorConvexTarget_of_unit_interval_kernel`.
Thus `cstarMatrixXLogXPositiveOperatorConvexTarget` and its all-finite-size
variant `cstarMatrixXLogXPositiveOperatorConvexAllFiniteTarget` are closed
locally. The block-column, range-projection/reflection, block-diagonal
star-algebra/order, block-diagonal CFC, compression-integral, and concrete
`x log x` corner substrates for the Hansen--Pedersen proof are also closed
through `CStarMatrixBridge` and `LiebTrace`. The active A1.5-B1 bottleneck now
moves to the Effros perspective/relative-entropy joint-convexity layer, then
Lieb trace concavity, trace-MGF domination, matrix Bernstein/Khintchine, and
CACM equation (2).
It also exposes the finite Kronecker lifts used in Tropp/Effros's
operator-perspective proof route: the maps `A ↦ A ⊗ I` and `A ↦ I ⊗ A` are
affine for real weighted sums, commute with each other, multiply to `A ⊗ H`,
and preserve positive definiteness when the source matrix is positive
definite. These facts are formalized as
`matrix_kronecker_left_identity_real_smul_add`,
`matrix_kronecker_right_identity_real_smul_add`,
`matrix_kronecker_left_identity_mul_right_identity`,
`matrix_kronecker_right_identity_mul_left_identity`,
`matrix_kronecker_left_right_commute`,
`matrix_kronecker_posDef_left_identity`, and
`matrix_kronecker_posDef_right_identity`, with the transpose-affine right-lift
variant `matrix_kronecker_right_identity_transpose_real_smul_add`. It also defines the vectorized
matrix representation `matrixVec`, proves
`matrix_kronecker_transpose_mulVec_matrixVec`, the action identity that
\(A\otimes B^{\mathsf T}\) represents \(M\mapsto AMB\), defines the vectorized
identity and the complex quadratic form, proves
`continuous_matrixComplexQuadraticForm`,
`matrixComplexQuadraticForm_re_nonneg_of_posSemidef`,
`matrixComplexQuadraticForm_re_mono_of_posSemidef_sub`, and
`matrixComplexQuadraticForm_re_mono_of_cstarMatrix_le`, and proves
`matrixComplexQuadraticForm_vecId_kronecker_transpose`, the trace-pairing
identity \(v_I^*(A\otimes B^{\mathsf T})v_I=\operatorname{tr}(AB)\). It also
proves the polynomial-power variants
`matrix_kronecker_transpose_pow`,
`matrix_kronecker_transpose_pow_mulVec_matrixVec`, `matrixVec_one`, and
`matrixComplexQuadraticForm_vecId_kronecker_transpose_pow`, showing that
powers of the Kronecker lift represent repeated left/right multiplication and
that \(v_I^*(A\otimes B^{\mathsf T})^k v_I=\operatorname{tr}(A^kB^k)\).
The finite polynomial packaging is recorded by
`matrixComplexQuadraticForm_sum`, `matrixComplexQuadraticForm_smul`, and
`matrixComplexQuadraticForm_vecId_kronecker_transpose_polynomial`; the same
statement in standard Lean polynomial-evaluation form is
`matrixComplexQuadraticForm_vecId_kronecker_transpose_aeval`, with polynomial
evaluation continuity supplied by `continuous_matrix_polynomial_aeval`.
The source-faithful superoperator-perspective polynomial layer is now also
local: `matrixVecId_inner_matrixVec`,
`matrix_transpose_conjTranspose_eq_self_of_isSelfAdjoint`,
`matrix_kronecker_transpose_isSelfAdjoint_of_isSelfAdjoint`,
`matrix_kronecker_transpose_posSemidef`, `matrix_kronecker_transpose_posDef`,
and `matrix_kronecker_inv_transpose_posDef` close the trace-pairing and domain
side conditions for `A ⊗ Bᵀ` and `X ⊗ (A⁻¹)ᵀ`.  The explicit
finite-matrix CFC wrapper `matrixSelfAdjointCfc`, its polynomial theorem
`matrixSelfAdjointCfc_polynomial`, and the Weierstrass wrappers
`exists_realPolynomial_near_log_on_Icc`,
`exists_realPolynomial_near_xlog_on_Icc`, and
`exists_realPolynomial_near_realEntropyKernel_on_Icc` provide the scalar
approximation layer.  The positive-spectrum wrappers
`matrix_posDef_spectrum_real_pos`,
`matrix_posDef_spectrum_real_subset_Icc`,
`exists_realPolynomial_tendstoUniformlyOn_realEntropyKernel_on_subset_Icc`,
and
`exists_realPolynomial_tendstoUniformlyOn_realEntropyKernel_spectrum_of_posDef`
turn that layer into a concrete uniformly convergent polynomial sequence on a
positive-definite matrix spectrum.  The right-multiplication perspective
formulas
`matrixComplexQuadraticForm_vecId_kronecker_transpose_pow_right`,
`matrixComplexQuadraticForm_vecId_kronecker_transpose_polynomial_right`,
`matrixComplexQuadraticForm_vecId_kronecker_transpose_aeval_right`, and
`matrixComplexQuadraticForm_vecId_matrixSelfAdjointCfc_kronecker_inv_transpose_realPolynomial_right`
prove the finite-polynomial trace identity for
\(p(L_XR_A^{-1})R_A\).  The analytic transfer hook
`tendsto_matrixComplexQuadraticForm_matrixSelfAdjointCfc_mul` and the
specialized theorem
`tendsto_superoperator_entropyKernel_of_realPolynomial_uniform_approx` show
that any explicit uniform polynomial approximation to the normalized entropy
kernel on the superoperator spectrum transfers those polynomial trace formulas
to the entropy-kernel CFC trace term.  The wrapper
`exists_realPolynomial_tendsto_superoperator_entropyKernel_trace_of_posDef`
combines the positive-spectrum approximation construction with this transfer,
while `matrixTrace_pow_mul_inv_pow_re_eq_sum` and
`matrixPolynomialTraceRatio_re_eq_sum` identify the finite-polynomial trace
approximants with the same eigenbasis-overlap weights used by the compact
relative-entropy formula.  The limiting superoperator overlap expansion,
source-faithful Umegaki trace representation, product-index perspective trace
equality, relative-entropy joint convexity, Lieb concavity, and one-step
trace-MGF layers are now closed locally.
It also
exposes the trace normalization needed by a future trace-representation step via
`matrix_trace_kronecker`, `matrix_trace_kronecker_left_identity`, and
`matrix_trace_kronecker_right_identity`. This is Kronecker/perspective
substrate only; it is not the Effros superoperator perspective theorem, the full
relative-entropy trace representation, or joint convexity.
For the next noncommutative Effros/Tropp perspective step, it also formalizes
left and right multiplication endomorphisms (`cstarMatrixLeftMul`,
`cstarMatrixRightMul`), their affine real-weighted-sum laws, their commutation
as `L_A R_B = R_B L_A`, and invertibility of these endomorphisms when the
underlying C-star matrix is a unit or strictly positive. It also proves the
product/power algebra needed by the future functional-calculus step:
`cstarMatrixLeftMul_mul`, `cstarMatrixRightMul_mul`,
`cstarMatrixLeftMul_pow`, and `cstarMatrixRightMul_pow`. It now also names the
ratio endomorphism `cstarMatrixLeftRightRatio`, i.e. the finite-dimensional
operator `L_X R_A^{-1}` with `A` supplied as a unit, and proves its action
formula and base-point normalization
(`cstarMatrixLeftRightRatio_apply`,
`cstarMatrixLeftRightRatio_apply_unit`,
`cstarMatrixLeftRightRatio_apply_of_isStrictlyPositive`). These are algebraic
operator-perspective foundations; they do not prove joint convexity.
Finally, it names the normalized relative-entropy variational objective
including the `Re tr A` constant required by the local relative-entropy
normalization, proves the optimizer-candidate equality
`cstarMatrixEntropyVariationalObjective_liebOptimizer`, reduces the normalized
variational formula to a named Klein-inequality-type nonnegativity foundation
(`cstarMatrixEntropyVariationalFormula_of_relativeEntropy_nonneg`), and
then reduces that nonnegativity foundation to the source-aligned generalized
Klein first-order trace inequality
(`cstarMatrixEntropyTraceFirstOrderConvexityOnStrictPositive`,
`cstarMatrixRelativeEntropyNonnegOnStrictPositive_of_entropyTraceFirstOrder`).
The converse direction and the equivalence are also recorded
(`cstarMatrixEntropyTraceFirstOrderConvexityOnStrictPositive_of_relativeEntropy_nonneg`,
`cstarMatrixEntropyTraceFirstOrderConvexityOnStrictPositive_iff_relativeEntropy_nonneg`),
so the two local noncommutative nonnegativity formulations are not treated as
separate hidden assumptions.  The file also closes the Hermitian spectral
overlap algebra used in Tropp's generalized Klein proof route:
`matrixTrace_diagonal_mul_mul_diagonal_mul_star`,
`matrixTrace_sum_diagonal_mul_mul_diagonal_mul_star_re`,
`matrixTrace_sum_hermitianCfc_mul_cfc_re`, and
`matrixTrace_sum_hermitianCfc_mul_cfc_nonneg_of_kernel_nonneg`.
The positive-spectrum scalar first-order specialization is also now local:
`matrixTrace_sum_hermitianCfc_mul_cfc_nonneg_of_eigen_kernel_nonneg`,
`matrixTrace_hermitianCfc_firstOrderKernel_sum_nonneg`,
`matrixTrace_hermitianCfc_firstOrderKernel_sum_nonneg_of_eigen`,
`realEntropy_firstOrderKernel_nonneg`, and
`matrixTrace_hermitianCfc_entropy_firstOrder_sum_nonneg`. The separated
Hermitian expression is now bridged to the compact entropy trace inequality by
`matrixTrace_hermitianCfc_entropy_firstOrder_compact_nonneg`, with
`matrix_isHermitian_cfc_id`, `matrix_isHermitian_cfc_xlog`, and
`matrixTrace_hermitianCfc_relativeEntropy_re_eq_sum` also identifying the
repository's compact matrix-relative-entropy trace with the scalar
relative-entropy kernel summed over squared eigenbasis overlaps. This narrows
the source-faithful superoperator bottleneck to matching the \(L_XR_A^{-1}\)
CFC trace term to that same overlap sum.  The polynomial-overlap bridge
`matrixTrace_pow_mul_inv_pow_re_eq_sum` and
`matrixPolynomialTraceRatio_re_eq_sum` now prove the same squared-overlap
weights for the finite-polynomial superoperator approximants
\(\operatorname{tr}(X^kA(A^{-1})^k)\) and
\(\sum_k p_k\operatorname{tr}(X^kA(A^{-1})^k)\); the remaining step is the
limit from those polynomial overlap formulas to the entropy-kernel CFC term.
`cstarMatrix_nonneg_to_matrix_posSemidef` and
`cstarMatrix_isStrictlyPositive_to_matrix_posDef` supplying the
C-star-to-plain-matrix positivity bridge. Consequently the local generalized
Klein theorem
`cstarMatrixEntropyTraceFirstOrderConvexityOnStrictPositive_of_hermitianCfc`,
relative-entropy nonnegativity
`cstarMatrixRelativeEntropyNonnegOnStrictPositive_of_hermitianCfc`, and the
normalized variational formula
`cstarMatrixEntropyVariationalFormula_of_hermitianCfc` are now proved locally.
It also names the intermediate target
foundations (`cstarMatrixEntropyVariationalObjective`,
`cstarMatrixRelativeEntropyNonnegOnStrictPositive`,
`cstarMatrixRelativeEntropyJointConvexOnStrictPositive`,
`cstarMatrixRelativeEntropyTraceRepresentationBySuperoperator`,
`cstarMatrixEntropyVariationalFormula`) and proves the conditional reductions
`liebTraceConcavityTarget_of_relativeEntropy_route` and
`liebTraceConcavityTarget_of_relativeEntropy_jointConvex`: joint convexity of
local matrix relative entropy now implies the local Lieb trace-concavity target.
The source-faithful superoperator trace representation and the product-index
Effros perspective equality bridge are now closed by
`cstarMatrixRelativeEntropyTraceRepresentationBySuperoperator_all`,
`cstarMatrixSuperoperatorPerspectiveTrace_eq_matrixSuperoperatorEntropyKernelTrace`,
and `cstarMatrixRelativeEntropyPerspectiveTraceRepresentation_all`.
This closes domain and trace-exponential well-formedness/normalization
vocabulary, one sanity-check Lieb subcase, the Jensen composition,
the generalized Klein first-order trace inequality, matrix relative-entropy
nonnegativity, the commutative scalar/vector/diagonal joint-convexity
subcases, the entropy variational formula, finite-dimensional
relative-entropy joint convexity
(`cstarMatrixRelativeEntropyJointConvexOnStrictPositive_all`), arbitrary
self-adjoint Lieb trace concavity (`liebTraceConcavityTarget_all`), and the
one-step Tropp trace-MGF inequality
(`FiniteProbability.expectationReal_trace_normed_exp_add_le`). This does not
prove matrix Bernstein/Khintchine or CACM equation (2). The new
`ElementwiseTraceMGF` module connects this one-step theorem to Algorithm 1's
squared-magnitude product trace law: it defines `sqMagSampleProbability`,
proves complex and C-star matrix marginal expectation adapters for a fixed
trace coordinate, proves the product-law last-sample conditioning identity
`sqMagTraceProbability_expectationReal_succ_last_eq`, and lifts the one-step
bound to iid sampled sums in
`sqMagTraceProbability_expectationReal_trace_normed_exp_add_sum_le`, and then
composes this with the finite-real matrix-exponential trace bridge in
`sqMagTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_add_sum_le`.
`ElementwiseSpectral.lean` now instantiates that finite-real trace-MGF theorem
with the actual Algorithm 1 self-adjoint dilation residual increments through
`sqMagTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_rectSelfAdjointDilation_elementwiseTraceResidual_le`.
It also specializes the repository's trace-exponential Markov/eigenvalue
interfaces to that scaled dilation residual in
`sqMagTraceProbability_eventProb_exists_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_elementwiseTraceResidual_ge_le`
and
`sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_elementwiseTraceResidual_lt_ge`.
`LiebTrace.lean` also now proves the scalar Bernstein parabola and its CFC
lift: `real_exp_mul_le_quadratic_of_nonneg_of_le_one` proves
`exp(a x) <= 1 + a x + (exp a - a - 1) x^2` for `a >= 0` and `x <= 1`,
`real_exp_mul_le_quadratic_scaled_of_nonneg_of_pos_of_le` proves the scaled
`R > 0` form, `cstarMatrix_cfc_quadratic_eq` normalizes the scalar quadratic
CFC expression as `I + theta X + beta X^2`, and
`cstarMatrix_cfc_real_exp_mul_le_bernstein_quadratic_of_spectrum_le` lifts the
explicit Bernstein coefficient to Loewner order under a real-spectrum upper
bound. The same file now proves the centered one-sample matrix-CGF/log-MGF
variance proxy:
`FiniteProbability.cstarMatrix_log_expectationCStarMatrix_normed_exp_real_smul_le_bernstein_variance_proxy`
shows
`log (E exp (theta • X)) <= g(theta,R) • E[X^2]` for self-adjoint
zero-mean samples with real spectrum bounded above by `R`; the support-aware
variants require that spectral upper bound only on positive-probability atoms.
`ElementwiseSpectral.lean` now instantiates this theorem for the truncated
Algorithm 1 self-adjoint dilation increments in
`sqMagSampleProbability_cstarMatrix_log_expectationCStarMatrix_normed_exp_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le`,
using the local one-sample C-star zero-mean theorem and the truncated
positive-support spectral bound. The same module now closes the two-sided
parameterized Bernstein skeleton: it proves the C-star dilation variance proxy
`sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le`,
the negative-support spectrum bound
`sqMagSampleProbability_neg_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_truncated_spectrum_le`,
the positive and negative scalar trace-MGF bounds
`sqMagTraceProbabilityFiniteRealTraceMGFLogBound_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le`
and
`sqMagTraceProbabilityFiniteRealTraceMGFLogBound_neg_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le`,
and the upper/two-sided eigenvalue tails
`sqMagTraceProbability_eventProb_exists_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_ge_le_exp`
and
`sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_exp`.
It also proves the explicit failure-probability corollary
`sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_one_sub_delta`,
using `T = log (2B/delta)` and the reusable algebra lemma
`real_exp_neg_log_two_mul_div_mul_self_add` from `MatrixConcentration.lean`.
For the square Drineas--Zouzias source route, the library now also proves the
sharper one-step variance scale without the older Frobenius-detour constants:
`sqMagProb_sum_vecNorm2Sq_rectMatMulVec_elementwiseSampleResidualIncrement_le_sharp`,
`sqMagProb_sum_vecNorm2Sq_transposeRectMatMulVec_elementwiseSampleResidualIncrement_le_sharp`,
`sqMagProb_sum_finiteQuadraticForm_rectSelfAdjointDilation_square_le_sharp_square`,
`sqMagProb_sum_rectSelfAdjointDilation_square_loewnerLe_scalar_id_sharp_square`,
and
`sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le_sharp_square`.
These feed the no-`sqrt 2` truncated support radius to give the square-matrix
source-aligned trace-MGF and two-sided tail skeletons
`sqMagTraceProbabilityFiniteRealTraceMGFLogBound_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le_sharp_square`,
`sqMagTraceProbabilityFiniteRealTraceMGFLogBound_neg_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le_sharp_square`,
`sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_exp_sharp_square`,
and
`sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_one_sub_delta_sharp_square`.
The scaled eigenvalue event is now converted into the rectangular spectral
event by
`algorithm1ScaledDilationAbsEigenvalueEvent_subset_exactSpectralEvent`, using
`finiteLoewnerLe_smul_id_of_finiteHermitianEigenvalues_le` and
`finiteLoewnerLe_of_smul_left_le_smul_id`.  The resulting high-probability
spectral corollary is
`sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_scaled_radius`,
with radius `log (2B/delta) / theta` for `theta > 0` and `0 < delta <= 1`.
The theta optimization dependency is also closed in the truncated exact route:
`real_bernstein_exact_radius_le_of_log_le` proves the scalar Bennett optimizer
`theta = log (1 + L*r/W) / L`, and
`sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bennett_radius`
uses it to prove the spectral event at an explicit radius `r` under the
corresponding Bennett budget.  The source-sharp square route has the matching
spectral conversions
`sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_scaled_radius_sharp_square`
and
`sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bennett_radius_sharp_square`,
which use `V = n*||Ahat||_F^2/s^2` and the no-`sqrt 2` support radius.  The
new scalar bridge `real_bennett_transform_lower_bound_two_add` proves the
conservative bound `(1+x) log(1+x)-x >= x^2/(2+x)`, and
`real_bennett_budget_of_quadratic_denominator_two_add` turns the simpler
condition `q <= r^2/(2W+L*r)` into the Bennett budget.  Composed with the
source-sharp square theorem, this gives
`sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bernstein_denominator_sharp_square`.
The sharper source denominator is now also formalized:
`real_bennett_transform_lower_bound_two_add_two_thirds` and
`real_bennett_budget_of_quadratic_denominator_two_add_two_thirds` prove the
`2W+(2/3)L*r` route, yielding
`sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bernstein_denominator_two_thirds_sharp_square`.
The same scalar file now also exposes
`real_bernstein_tail_le_half_delta_of_quadratic_budget`, which converts a
Bennett sample-size inequality directly into a one-sided `δ/2` exponential
tail budget; Algorithm 2's leverage row-sampling sample-budget theorem reuses
this bridge for its upper and lower tails.
The sample-budget theorem
`sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_source_sample_budget_sharp_square`
proves the truncated exact event from
`14*n*||A||_F^2*log(2(2n)/delta) <= s*eps^2`, and
`sqMagTraceProbability_eventProb_algorithm1ExactTruncatedSpectralEvent_ge_one_sub_delta_source_sample_budget_sharp_square`
adds the deterministic truncation transfer to the original matrix.  The FP
variant
`sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralEvent_ge_one_sub_delta_source_sample_budget_sharp_square`
transfers the same probability to rounded arithmetic under an explicit
entrywise FP perturbation budget.  The support-aware theorem
`sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralEvent_ge_one_sub_delta_source_sample_budget_gamma_square`
derives that budget from local `gamma`/hit-count stability on the
probability-one positive-probability support of the sampler, with only
`gammaValid fp s` and `gammaValid fp (s+1)` as FP validity assumptions.
The scalar-radius corollaries
`sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralRadius_ge_one_sub_delta_source_sample_budget_gamma_square`
and
`sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralRadius_ge_one_sub_delta_source_sample_budget_explicit_gamma_square`
expand that internal budget matrix into readable terms: first
`eps + n*(||Ahat||_F^2/tau)*gamma fp (s+1)`, then the source-only bound
`eps + (2*n^2*||A||_F^2/eps)*gamma fp (s+1)` for
`tau = eps/(2n)`.
For the literal, nontruncated Algorithm 1 law
`p_ij = A_ij^2/||A||_F^2`, the theorem
`sqMagTraceProbability_eventProb_algorithm1FlSpectralRadius_ge_one_sub_delta_frob_explicit_gamma_square`
proves a faithful rounded spectral-radius corollary with no hard-thresholded
matrix.  It uses the weaker Frobenius/Markov sample budget
`n^2*||A||_F^2/(s*eps^2) <= delta` and an explicit nonzero-entry floor
`alpha <= |A_ij|` for nonzero entries, giving radius
`eps + n*(||A||_F^2/alpha)*gamma fp (s+1)`.  This faithful corollary is not
the sharp CACM equation (2) matrix-Bernstein theorem.
The literal support-radius route now also has an entry-floor simplification.
The theorem
`sqMagTraceProbability_eventProb_algorithm1FlSpectralRadius_literal_ge_one_sub_delta_bernstein_denominator_gamma_entry_floor`
uses the exact squared-magnitude law and the readable support radius
`s^-1*||A||_F + m*n*||A||_F^2/(s*alpha)`, under
`alpha <= |A_ij|` for nonzero entries.  The rounded implementation radius is
`r + sqrt(m*n)*(m*n*||A||_F^2/alpha)*gamma fp (s+1)`, with all sampled-update
and residual arithmetic charged and no probability-computation error term.
The sharper literal source-rate corollaries
`sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_ge_one_sub_delta_source_sample_budget_no_small_entries_square`
and
`sqMagTraceProbability_eventProb_algorithm1FlSpectralRadius_ge_one_sub_delta_source_sample_budget_no_small_entries_square`
recover the paper-style sample budget
`14*n*||A||_F^2*log(2(2n)/delta) <= s*eps^2` for the literal law
`p_ij = A_ij^2/||A||_F^2`, under the explicit condition
`eps/(2n) <= |A_ij|` for every nonzero entry.  Under that condition the
source threshold is the identity on `A`, so no truncated sampling distribution
is used; the rounded radius is
`eps + (2*n^2*||A||_F^2/eps)*gamma fp (s+1)`.
The literal untruncated source-uniform route also has a formal small-entry
obstruction.  For the exact input `[1, (|L|+2)^-1]`, the all-copy support
event fails with probability at least the tiny-entry mass, and for any positive
sample count `s` the all-tiny trace has product-law mass `p_tiny^s` and lies
outside the exact spectral event at radius `L`.  The theorem
`sqMagTraceProbability_algorithm1ExactSpectralEvent_all_tiny_smallEntry_delta_ge`
therefore forces any claimed `1 - delta` exact spectral-event lower bound on
that family to satisfy `p_tiny^s <= delta`; the logarithmic wrapper
`sqMagTraceProbability_algorithm1ExactSpectralEvent_all_tiny_smallEntry_log_delta_le`
gives `log(1/delta) <= s * log(1/p_tiny)` for positive `delta`, and
`sqMagTraceProbability_algorithm1ExactSpectralEvent_all_tiny_smallEntry_sample_count_ge`
uses `0 < p_tiny < 1` to prove the divided lower-bound form
`log(1/delta)/log(1/p_tiny) <= s`.
The contradiction wrappers
`sqMagTraceProbability_not_algorithm1ExactSpectralEvent_all_tiny_smallEntry_of_delta_lt_pow`
and
`sqMagTraceProbability_not_algorithm1ExactSpectralEvent_all_tiny_smallEntry_of_sample_count_lt`
state the same obstruction as impossibility theorems: if
`delta < p_tiny^s`, or if positive `delta` and
`s < log(1/delta)/log(1/p_tiny)`, then the claimed `1-delta` lower bound for
the exact spectral event on this family cannot hold.
The sharper probability-surface wrappers
`sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_all_tiny_smallEntry_le_one_sub_pow`,
`sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_all_tiny_smallEntry_lt_one`,
and
`exists_delta_not_sqMagTraceProbability_algorithm1ExactSpectralEvent_all_tiny_smallEntry`
state this as a direct success-probability cap:
`P(E_spec) <= 1 - p_tiny^s`, hence `P(E_spec) < 1`, and therefore for every
fixed positive sample count there exists a positive `delta` for which the
advertised `1-delta` lower bound cannot hold.
The concrete witness
`sqMagTraceProbability_not_algorithm1ExactSpectralEvent_rect_source_budget_witness`
sets `m=1`, `n=2`, `s=1`, radius `100`, `delta=1/30000`, and
`A=[1,1/102]`: the rectangular source-style budget is true in exact
arithmetic, but the literal exact spectral-event lower bound is impossible.
The wrapper
`not_forall_algorithm1ExactSpectralEvent_of_rect_source_budget_one_div_30000`
refutes the universal source-budget-only implication at those fixed
parameters for all exact inputs with positive squared-magnitude denominator.
This is exact-law obstruction evidence, not a floating-point theorem and not a
substitute for a genuine matrix-tail proof.
Remaining full-paper blocker context is described inline in the RandNLA sections
below; checked declarations are indexed in
[`docs/LIBRARY_LOOKUP.md`](docs/LIBRARY_LOOKUP.md). The spectral bridge now also
proves that
local PSD is equivalent to nonnegative Hermitian eigenvalues, and that
`M <= L I` is equivalent to nonnegativity of the Hermitian eigenvalues of
`L I - M`, with a named scalar-identity difference eigenvalue family for
reuse in event definitions. It also proves the converse upper-bound bridge:
pointwise Hermitian eigenvalue upper bounds imply `M <= L I`. The source-alignment
layer for Drineas-Zouzias also
formalizes the truncated variant explicitly: hard-thresholding at `eps/(2n)`
has Frobenius/operator cost at most `eps/2`, and any future half-budget
spectral theorem for the sampled truncated matrix transfers to exact and
floating-point residual events against the original matrix.  The truncated
route also now has the probability-one support and bounded-increment
prerequisites needed by a future matrix-Bernstein proof: retained samples have
positive squared-magnitude probability, hard-thresholding does not increase the
Frobenius norm, and every retained one-step residual increment has explicit
rectangular, self-adjoint-dilation operator, and squared-Loewner bounds.  The
self-adjoint-dilation bounded-operator and bounded-square events are also
combined into a single probability-one Bernstein-boundedness event. The
truncated route also has a support-aware finite-test quadratic-form MGF theorem
whose one-step bound is discharged from positive probability under the
truncated squared-magnitude law.
The library also includes a deterministic spectral-transfer layer for equation
(2)-style rectangular residual bounds: if a future exact matrix-concentration
theorem proves the sampled residual bound in `rectOpNorm2Le` form, then the
floating-point residual bound follows by adding the Frobenius norm of the
proved entrywise stability budget. This transfer does not prove matrix
Bernstein or the exact equation (2) concentration theorem.
There is also a Frobenius residual bridge: an exact Frobenius residual event
implies the corresponding rectangular operator event, and then the same
floating-point transfer applies.
The canonical squared-magnitude product trace law now proves a nonconditional
Frobenius residual second-moment bound,
`E ||A - Atilde||_F^2 <= (m*n/s) ||A||_F^2`, plus the corresponding Markov
high-probability Frobenius/operator transfer. This is intentionally documented
as weaker than the CACM equation (2) spectral-norm concentration theorem.
A second scalar route proves a simultaneous entrywise residual event by a
finite union bound over all `(i,j)` entries, then transfers that event to the
same rectangular operator predicate. This is also weaker than equation (2), but
it is a reusable foundation for future scalar-to-matrix concentration work.

Key entry points:

```lean
import LeanFpAnalysis.FP.Algorithms.RandNLA
open LeanFpAnalysis.FP

#check fl_elementwiseTraceSketch_sqMag_error_bound
#check sqMagTraceProbability_expectationReal_elementwiseTraceSketch_nonzero_entry
#check sqMagTraceProbability_expectationReal_elementwiseTraceSketch_entry
#check sqMagTraceProbability_expectationReal_elementwiseTraceSketch_matrix
#check elementwiseSampleResidualIncrement
#check elementwiseTraceResidual_eq_sum_sampleResidualIncrement
#check sqMagProb_sum_elementwiseSampleResidualIncrement_entry_eq_zero
#check sqMagProb_sum_elementwiseSampleContribution_entry_sq_le
#check sqMagProb_sum_elementwiseSampleResidualIncrement_entry_sq_le
#check sqMagProb_sum_elementwiseSampleResidualIncrement_frob_sq_le
#check sqMagTraceProbability_expectationReal_elementwiseTraceResidual_entry_eq_zero
#check rectMatMulVec_elementwiseTraceResidual_eq_sum_sampleResidualIncrement
#check sqMagProb_sum_rectMatMulVec_elementwiseSampleResidualIncrement_eq_zero
#check sqMagProb_sum_vecNorm2Sq_rectMatMulVec_elementwiseSampleResidualIncrement_le
#check sqMagTraceProbability_expectationReal_rectMatMulVec_elementwiseTraceResidual_eq_zero
#check rectOpNorm2Le
#check rectOpNorm2Le_of_selfAdjointDilation_loewnerLe_scalar_id
#check IsSymmetricFiniteMatrix.to_matrix_isSymm
#check Matrix_isSymm.to_IsSymmetricFiniteMatrix
#check IsSymmetricFiniteMatrix.to_matrix_isHermitian
#check Matrix_isHermitian.to_IsSymmetricFiniteMatrix
#check finitePSD.to_matrix_posSemidef
#check Matrix_posSemidef.to_finitePSD
#check finitePSD_iff_matrix_posSemidef_of_symmetric
#check finiteLoewnerLe.to_matrix_posSemidef_sub
#check Matrix_posSemidef_sub.to_finiteLoewnerLe
#check finiteLoewnerLe_iff_matrix_posSemidef_sub_of_symmetric
#check finiteHermitianEigenvalues
#check finiteHermitianEigenvalues_mem_spectrum_real
#check finiteTrace_eq_sum_finiteHermitianEigenvalues
#check finiteMatrixExp
#check finiteMatrixExp_smul_finiteIdMatrix
#check finiteTrace_finiteMatrixExp_smul_finiteIdMatrix
#check finiteMatrixExp_symmetric
#check finiteDiagonal
#check finiteMatrixExp_finiteDiagonal
#check finiteTrace_finiteMatrixExp_finiteDiagonal
#check finiteHermitianCfcExp
#check finiteTrace_finiteHermitianCfcExp_eq_sum_exp_finiteHermitianEigenvalues
#check finiteTrace_finiteMatrixExp_eq_sum_exp_finiteHermitianEigenvalues
#check finiteTrace_finiteMatrixExp_neg_eq_sum_exp_neg_finiteHermitianEigenvalues
#check finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq
#check finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one
#check finiteHermitianEigenvalues_le_of_finiteLoewnerLe_smul_id
#check finiteTrace_finiteMatrixExp_le_card_mul_exp_of_finiteLoewnerLe_smul_id
#check finiteTrace_finiteMatrixExp_neg_le_card_mul_exp_of_neg_finiteLoewnerLe_smul_id
#check exp_le_finiteTrace_finiteMatrixExp_of_finiteHermitianEigenvalue_ge
#check finiteTrace_finiteMatrixExp_nonneg
#check exp_neg_le_finiteTrace_finiteMatrixExp_neg_of_finiteHermitianEigenvalue_le
#check finiteTrace_finiteMatrixExp_neg_nonneg
#check FiniteProbability.eventProb_exists_finiteHermitianEigenvalue_ge_le_exp_neg_mul_expected_trace_exp
#check FiniteProbability.eventProb_exists_finiteHermitianEigenvalue_ge_le_exp_neg_mul_trace_bound
#check FiniteProbability.eventProb_forall_finiteHermitianEigenvalue_lt_ge_one_sub_exp_neg_mul_expected_trace_exp
#check FiniteProbability.eventProb_forall_finiteHermitianEigenvalue_lt_ge_one_sub_exp_neg_mul_trace_bound
#check FiniteProbability.eventProb_exists_finiteHermitianEigenvalue_le_le_exp_mul_expected_trace_exp_neg
#check FiniteProbability.eventProb_exists_finiteHermitianEigenvalue_le_le_exp_mul_trace_bound
#check FiniteProbability.eventProb_forall_finiteHermitianEigenvalue_gt_ge_one_sub_exp_mul_expected_trace_exp_neg
#check FiniteProbability.eventProb_forall_finiteHermitianEigenvalue_gt_ge_one_sub_exp_mul_trace_bound
#check FiniteProbability.eventProb_forall_abs_finiteHermitianEigenvalue_lt_ge_one_sub_exp_neg_mul_expected_trace_exp_add
#check FiniteProbability.eventProb_forall_abs_finiteHermitianEigenvalue_lt_ge_one_sub_exp_neg_mul_trace_bound_add
#check finiteComplexCStarMatrix
#check finiteComplexCStarMatrix_zero
#check finiteComplexCStarMatrix_add
#check finiteComplexCStarMatrix_isSelfAdjoint_of_symmetric
#check finiteComplexCStarMatrix_sub
#check finiteComplexCStarMatrix_finset_sum
#check finiteComplexCStarMatrix_finiteIdMatrix
#check finiteComplexCStarMatrix_smul_finiteIdMatrix
#check finiteComplexCStarMatrixRingHom
#check finiteComplexCStarMatrixRingHom_continuous
#check finiteComplexCStarMatrix_finiteMatrixExp
#check cstarMatrix_complex_finiteDimensional
#check finiteComplexCStarMatrix_nonneg_of_finitePSD
#check cstarMatrix_nonneg_of_matrix_posSemidef
#check cstarMatrix_le_of_matrix_le
#check finiteComplexCStarMatrix_le_of_finiteLoewnerLe
#check cstarMatrix_pos_real_smul_one_isStrictlyPositive
#check finiteComplexCStarMatrix_add_pos_smul_one_isStrictlyPositive_of_finitePSD
#check finiteComplexCStarMatrix_add_smul_one_le_of_finiteLoewnerLe
#check cstarMatrix_log_le_log
#check cstarMatrix_log_normedSpace_exp_of_isSelfAdjoint
#check cstarMatrix_log_cfc_complex_exp_of_isSelfAdjoint
#check cstarMatrix_log_cfc_real_exp_of_isSelfAdjoint
#check cstarMatrix_normedSpace_exp_isStrictlyPositive_of_isSelfAdjoint
#check cstarMatrix_cfc_complex_exp_isStrictlyPositive_of_isSelfAdjoint
#check cstarMatrix_cfc_real_exp_isStrictlyPositive_of_isSelfAdjoint
#check real_exp_quadratic_remainder_monotone
#check real_exp_sub_self_sub_one_nonneg
#check real_sq_div_two_le_exp_sub_self_sub_one_of_nonneg
#check real_exp_le_one_add_self_add_sq_div_two_of_nonpos
#check real_exp_tail_two_hasSum
#check real_exp_mul_le_quadratic_of_nonneg_of_nonneg_of_le_one
#check real_exp_mul_le_quadratic_of_nonneg_of_le_one
#check real_exp_mul_le_quadratic_scaled_of_nonneg_of_pos_of_le
#check cstarMatrix_cfc_quadratic_eq
#check cstarMatrix_cfc_real_exp_mul_le_quadratic_of_spectrum
#check cstarMatrix_cfc_real_exp_mul_le_bernstein_quadratic_of_spectrum_le
#check cstarMatrix_real_smul_isSelfAdjoint
#check cstarMatrix_cfc_real_exp_mul_eq_normedSpace_exp_real_smul
#check cstarMatrix_selfAdjoint_mul_self_nonneg
#check cstarMatrix_one_add_le_normedSpace_exp_of_nonneg
#check cstarMatrix_log_one_add_le_self_of_nonneg
#check FiniteProbability.expectationCStarMatrix_real_smul
#check FiniteProbability.expectationCStarMatrix_cfc_real_exp_mul_le_bernstein_variance_proxy
#check FiniteProbability.cstarMatrix_log_expectationCStarMatrix_cfc_real_exp_mul_le_bernstein_variance_proxy
#check FiniteProbability.cstarMatrix_log_expectationCStarMatrix_normed_exp_real_smul_le_bernstein_variance_proxy
#check cstarMatrix_spectrum_nonneg_of_nonneg
#check cstarMatrix_normedSpace_exp_log_of_isStrictlyPositive
#check cstarMatrix_cfc_complex_exp_log_of_isStrictlyPositive
#check cstarMatrix_cfc_real_exp_log_of_isStrictlyPositive
#check finiteComplexCStarMatrix_regularized_log_le_log_of_finiteLoewnerLe
#check cstarMatrixTrace
#check cstarMatrixTrace_neg
#check cstarMatrixTrace_sub
#check cstarMatrixTrace_mul_comm
#check cstarMatrixTrace_star_mul_self_re_nonneg
#check cstarMatrixTrace_re_nonneg_of_nonneg
#check cstarMatrixTrace_re_mono
#check cstarMatrixTrace_im_eq_zero_of_isSelfAdjoint
#check cstarMatrixTrace_finiteComplexCStarMatrix
#check cstarMatrixTrace_normed_exp_finiteComplexCStarMatrix
#check cstarMatrixTrace_normed_exp_finiteComplexCStarMatrix_re
#check cstarMatrixTrace_finiteComplexCStarMatrix_re_nonneg_of_finitePSD
#check cstarMatrixTrace_finiteComplexCStarMatrix_re_mono_of_finiteLoewnerLe
#check cstarMatrixTrace_cfc_exp_algebraMap
#check cstarMatrixTrace_cfc_exp_real_smul_one
#check FiniteProbability.expectationComplex
#check FiniteProbability.expectationComplex_ofReal
#check FiniteProbability.expectationComplex_re
#check FiniteProbability.exists_prob_pos
#check FiniteProbability.expectationReal_le_of_concaveOn
#check FiniteProbability.expectationReal_exp_pos
#check FiniteProbability.hasDerivAt_expectationReal_exp_mul
#check FiniteProbability.hasDerivAt_log_expectationReal_exp_mul
#check FiniteProbability.entropyReal
#check FiniteProbability.entropyReal_const
#check FiniteProbability.entropyReal_exp_mul_eq
#check FiniteProbability.boolUniformProbability
#check FiniteProbability.boolUniformProbability_prob
#check FiniteProbability.boolUniformProbability_expectationReal
#check FiniteProbability.entropyReal_boolUniformProbability_eq
#check FiniteProbability.twoPointEntropy_le_sq_sub_div_of_pos
#check FiniteProbability.entropyReal_boolUniformProbability_sq_le_sq_sub_of_pos
#check FiniteProbability.abs_expectationReal_mul_le_sqrt_mul_sqrt
#check FiniteProbability.sqrt_expectationReal_sq_add_le
#check FiniteProbability.abs_sqrt_expectationReal_sq_sub_le_sqrt_expectationReal_sub_sq
#check FiniteProbability.boolUniformProbability_abs_sqrt_expectationReal_sq_sub_le_sqrt_expectationReal_sub_sq
#check FiniteProbability.entropyReal_prod_boolUniformProbability_sq_le_coordinate_add_entropy
#check FiniteProbability.entropyReal_prod_boolUniformProbability_sq_le_lifted_diff_sum_add
#check FiniteProbability.prod_expectationReal_eq
#check FiniteProbability.prod_expectationReal_fst_eq
#check FiniteProbability.entropyReal_prod_eq_expectation_entropyReal_add_entropyReal_expectation
#check FiniteProbability.log_mgf_differential_le_of_entropyReal_exp_mul_le
#check FiniteProbability.log_mgf_div_sub_quadratic_antitoneOn_of_differential_le
#check FiniteProbability.tendsto_log_mgf_div_nhdsGT_zero
#check FiniteProbability.log_mgf_le_mean_add_quadratic_of_differential_le
#check FiniteProbability.log_mgf_le_mean_add_quadratic_of_entropyReal_exp_mul_le
#check FiniteProbability.expectationReal_exp_centered_le_exp_of_log_mgf_le
#check FiniteProbability.eventProb_real_le_ge_one_sub_exp_of_mgf_bound
#check FiniteProbability.eventProb_real_le_mean_add_ge_one_sub_exp_sq_of_subgaussian_mgf
#check FiniteProbability.eventProb_real_le_mean_add_ge_one_sub_exp_sq_of_log_mgf_bound
#check FiniteProbability.eventProb_real_le_mean_add_ge_one_sub_exp_sq_of_entropyReal_exp_mul_le
#check real_exp_sub_one_le_mul_exp
#check real_abs_exp_sub_exp_le_abs_sub_mul_exp_add_exp
#check real_exp_half_sub_sq_le_two_mul_half_diff_sq
#check FiniteProbability.expectationCStarMatrix
#check FiniteProbability.cstarMatrixTrace_expectationCStarMatrix
#check FiniteProbability.expectationCStarMatrix_finiteComplexCStarMatrix
#check FiniteProbability.expectationCStarMatrix_eq_sum_smul
#check FiniteProbability.expectationCStarMatrix_eq_sum_real_smul
#check FiniteProbability.expectationReal_le_of_concaveOn_expectationCStarMatrix
#check FiniteProbability.expectationReal_trace_cfc_exp_add_log_le_of_concaveOn
#check FiniteProbability.expectationCStarMatrix_nonneg
#check FiniteProbability.expectationCStarMatrix_isStrictlyPositive
#check FiniteProbability.expectationCStarMatrix_mono
#check FiniteProbability.expectationCStarMatrix_add_pos_smul_one_isStrictlyPositive
#check strictPositiveCStarMatrixCone
#check cstarMatrix_isStrictlyPositive_pos_real_smul
#check cstarMatrix_nonneg_nonneg_real_smul
#check cstarMatrix_isStrictlyPositive_pos_nonneg_real_smul_add
#check strictPositiveCStarMatrixCone_convex
#check cstarMatrix_log_isSelfAdjoint
#check liebTraceArgument_isSelfAdjoint
#check liebTraceArgument_isStarNormal
#check liebTraceCfcExp_nonneg
#check liebTraceCfcExp_isStrictlyPositive
#check liebTraceFunctional_trace_im_eq_zero
#check liebTraceFunctional
#check liebTraceFunctional_nonneg
#check liebTraceFunctional_eq_normedSpace_exp
#check liebTraceFunctional_zero_eq_trace
#check liebTraceConcavityTarget
#check liebTraceConcavityTarget_zero
#check FiniteProbability.expectationReal_trace_normed_exp_add_le_of_liebTraceConcavityTarget
#check realRelativeEntropy
#check realRelativeEntropy_nonneg
#check finite_log_sum_inequality
#check realRelativeEntropy_jointConvex
#check finiteRealRelativeEntropy
#check finiteRealRelativeEntropy_nonneg
#check finiteRealRelativeEntropy_jointConvex
#check cstarMatrixDiagonalStarAlgHom
#check cstarMatrixDiagonalStarAlgHom_continuous
#check cstarMatrixRealDiagonal
#check cstarMatrixRealDiagonal_smul_add
#check cstarMatrixTrace_realDiagonal
#check cstarMatrix_log_realDiagonal
#check cstarMatrixRelativeEntropy
#check cstarMatrixRelativeEntropy_self
#check cstarMatrixRelativeEntropy_realDiagonal
#check cstarMatrixRelativeEntropy_realDiagonal_nonneg
#check cstarMatrixRelativeEntropy_realDiagonal_jointConvex
#check cstarMatrixRelativeEntropy_algebraMap_real
#check cstarMatrixRelativeEntropy_algebraMap_real_nonneg
#check real_xlog_eq_sub_one_mul_realNormalizedLogKernel
#check real_xlog_eq_sub_one_mul_normalizedKernel_setIntegral
#check real_xlog_eq_unit_interval_xlog_kernel_integral
#check real_unit_interval_xlog_integrand_eq_affine_add_shifted_inv
#check cstarMatrix_cfc_unit_interval_xlog_integrand_eq_affine_add_shifted_inv
#check real_unit_interval_xlog_kernel_integrand_eq_affine_add_shifted_inv
#check cstarMatrix_cfc_unit_interval_xlog_kernel_integrand_eq_affine_add_shifted_inv
#check cstarMatrix_cfc_inv_convex_isStrictlyPositive
#check cstarMatrix_cfc_shifted_inv_eq_cfc_inv_add_smul_one
#check cstarMatrix_cfc_shifted_inv_convex_nonneg
#check continuousOn_uncurry_unit_interval_xlog_kernel_spectrum
#check real_abs_sub_one_le_max_one_of_pos_le
#check real_unit_interval_xlog_kernel_abs_le_max_sq_of_le
#check real_unit_interval_xlog_kernel_spectrum_norm_le_max_sq
#check ae_unit_interval_xlog_kernel_spectrum_norm_le_max_sq
#check hasFiniteIntegral_const_max_one_spectrum_bound_sq
#check cstarMatrix_cfc_xlog_eq_unit_interval_xlog_kernel_integral
#check cstarMatrix_cfc_unit_interval_xlog_integrand_convex_of_pos_lt_one
#check cstarMatrix_cfc_unit_interval_xlog_kernel_integrand_convex_of_pos_lt_one
#check cstarMatrixXLogXPositiveOperatorConvexTarget_of_unit_interval_kernel
#check cstarMatrixXLogXPositiveOperatorConvexAllFiniteTarget_of_unit_interval_kernel
#check cstarMatrix_compression_setIntegral
#check cstarMatrixColumnPair_reflectionAverage_xlog_kernel_corner_of_sum
#check cstarMatrixColumnPair_reflectionAverage_xlog_corner_of_sum
#check cstarMatrixXLogXHansenPedersenJensenTarget_of_reflectionAverage_xlog_corner
#check cstarMatrixXLogXHansenPedersenJensenTarget_of_unit_interval_kernel
#check realEntropyKernel
#check cstarMatrixEntropyKernelPositiveOperatorConvexTarget
#check cstarMatrixEntropyKernelPositiveOperatorConvexAllFiniteTarget
#check cstarMatrixEntropyKernelPositiveOperatorConvexTarget_of_xlog
#check cstarMatrixEntropyKernelPositiveOperatorConvexTarget_of_unit_interval_kernel
#check cstarMatrixEntropyKernelPositiveOperatorConvexAllFiniteTarget_of_unit_interval_kernel
#check cstarMatrixEntropyKernelHansenPedersenJensenTarget
#check cstarMatrix_cfc_realEntropyKernel_eq_xlog_sub_id_add_one
#check cstarMatrixEntropyKernelHansenPedersenJensenTarget_of_xlog
#check cstarMatrixEntropyKernelHansenPedersenJensenTarget_of_unit_interval_kernel
#check cstarMatrixPositiveSqrt
#check cstarMatrixPositiveInvSqrt
#check cstarMatrixPositiveSqrt_isSelfAdjoint
#check cstarMatrixPositiveInvSqrt_isSelfAdjoint
#check continuousOn_real_inv_sqrt_spectrum_of_isStrictlyPositive
#check cstarMatrixPositiveSqrt_mul_self
#check cstarMatrixPositiveInvSqrt_mul_sqrt
#check cstarMatrixPositiveSqrt_mul_invSqrt
#check cstarMatrixPositiveInvSqrt_isUnit
#check complex_ofReal_sqrt_mul_self_of_nonneg
#check cstarMatrixPositiveSqrt_isStrictlyPositive
#check cstarMatrixPositiveInvSqrt_mul_self_mul
#check cstarMatrixPositiveInvSqrt_mul_self_eq_unit_inv
#check cstarMatrixPositiveSqrt_commute_unit_inv
#check cstarMatrixPositiveInvSqrt_conj_isStrictlyPositive
#check cstarMatrixXLogXHansenPedersenJensenTarget_of_transfer
#check cstarMatrixXLogXHansenPedersenJensenTarget_of_allFiniteTransfer
#check cstarMatrix_compression_mono
#check cstarMatrixColumnPair_reflectionAverage_cfc_le_average_of_sum
#check cstarMatrixColumnPair_reflectionAverage_compressed_cfc_le_compressed_of_sum
#check cstarMatrix_units_inv_mul_rect_eq_mul_units_inv_of_mul_eq
#check cstarMatrix_cfc_shifted_inv_mul_rect_eq_mul_cfc_shifted_inv_of_mul_eq
#check cstarMatrixColumnPair_reflectionAverage_shifted_inv_corner_of_sum
#check matrixVecId_inner_matrixVec
#check matrix_transpose_conjTranspose_eq_self_of_isSelfAdjoint
#check matrix_kronecker_transpose_isSelfAdjoint_of_isSelfAdjoint
#check matrix_kronecker_transpose_posSemidef
#check matrix_kronecker_transpose_posDef
#check matrix_kronecker_inv_transpose_posDef
#check matrixSelfAdjointCfc
#check matrixSelfAdjointCfc_polynomial
#check exists_realPolynomial_near_log_on_Icc
#check exists_realPolynomial_near_xlog_on_Icc
#check exists_realPolynomial_near_realEntropyKernel_on_Icc
#check matrix_posDef_spectrum_real_pos
#check matrix_posDef_spectrum_real_subset_Icc
#check exists_realPolynomial_tendstoUniformlyOn_realEntropyKernel_on_subset_Icc
#check exists_realPolynomial_tendstoUniformlyOn_realEntropyKernel_spectrum_of_posDef
#check matrixComplexQuadraticForm_vecId_kronecker_transpose_pow_right
#check matrixComplexQuadraticForm_vecId_kronecker_transpose_polynomial_right
#check matrixComplexQuadraticForm_vecId_kronecker_transpose_aeval_right
#check matrixComplexQuadraticForm_vecId_matrixSelfAdjointCfc_kronecker_transpose_realPolynomial
#check matrixComplexQuadraticForm_vecId_matrixSelfAdjointCfc_kronecker_inv_transpose_realPolynomial_right
#check tendsto_matrixComplexQuadraticForm_matrixSelfAdjointCfc_mul
#check tendsto_superoperator_entropyKernel_of_realPolynomial_uniform_approx
#check exists_realPolynomial_tendsto_superoperator_entropyKernel_trace_of_posDef
#check matrixComplexQuadraticForm_re_nonneg_of_posSemidef
#check matrixComplexQuadraticForm_re_mono_of_posSemidef_sub
#check matrixComplexQuadraticForm_re_mono_of_cstarMatrix_le
#check matrixComplexQuadraticForm_add
#check matrixTrace_pow_mul_inv_pow_re_eq_sum
#check matrixPolynomialTraceRatio_re_eq_sum
#check realRelativeEntropy_eq_mul_realEntropyKernel_mul_inv
#check tendsto_matrixPolynomialTraceRatio_overlap_sum_of_uniform_approx
#check exists_realPolynomial_tendsto_superoperator_entropyKernel_trace_and_overlap_of_posDef
#check matrixSuperoperatorEntropyKernelTrace
#check matrixSuperoperatorEntropyKernelOverlapExpansion
#check matrixSuperoperatorEntropyKernelOverlapExpansion_of_nonempty
#check matrixSuperoperatorEntropyKernelOverlapExpansion_of_isEmpty
#check matrixSuperoperatorEntropyKernelOverlapExpansion_all
#check matrixRelativeEntropyTraceRepresentation_of_superoperator_overlap
#check matrix_kronecker_left_identity_real_smul_add
#check matrix_kronecker_right_identity_real_smul_add
#check matrix_kronecker_right_identity_transpose_real_smul_add
#check matrix_kronecker_left_identity_mul_right_identity
#check matrix_kronecker_right_identity_mul_left_identity
#check matrix_kronecker_left_right_commute
#check matrix_kronecker_posDef_left_identity
#check matrix_kronecker_posDef_right_identity
#check cstarMatrixSuperoperatorLeftLift
#check cstarMatrixSuperoperatorRightLift
#check cstarMatrixSuperoperatorLeftLift_real_smul_add
#check cstarMatrixSuperoperatorRightLift_real_smul_add
#check cstarMatrixSuperoperatorLeftLift_isStrictlyPositive
#check cstarMatrixSuperoperatorRightLift_isStrictlyPositive
#check cstarMatrixSuperoperatorLeftLift_rightLift_commute
#check cstarMatrixSuperoperatorPositiveInvSqrtRightLift_commute_leftLift
#check cstarMatrixSuperoperatorPositiveSqrtRightLift_commute_leftLift
#check cstarMatrixSuperoperatorPerspective_normalizedArgument_reorder
#check cstarMatrixSuperoperatorPerspective_normalizedArgument_eq_leftLift_mul_rightLift_unit_inv
#check cstarMatrixSuperoperatorLeftLift_mul_rightLift_unit_inv_commute_positiveSqrtRightLift
#check cstarMatrixSuperoperatorEntropyKernelCfc_ratio_commute_positiveSqrtRightLift
#check cstarMatrixSuperoperatorPerspective_outerSqrt_cfc_ratio_mul_outerSqrt
#check cstarMatrixSuperoperatorPerspective_eq_cfc_ratio_mul_rightLift
#check cstarMatrix_unit_inv_to_matrix
#check cstarMatrixSuperoperatorRightLift_unit_inv_to_matrix
#check cstarMatrixSuperoperatorPerspectiveTrace_eq_matrixSuperoperatorEntropyKernelTrace
#check cstarMatrixSuperoperatorPerspectiveTrace
#check cstarMatrixSuperoperatorPerspectiveTrace_jointConvex
#check cstarMatrixRelativeEntropyPerspectiveTraceRepresentation
#check cstarMatrixRelativeEntropyPerspectiveTraceRepresentation_all
#check cstarMatrixRelativeEntropyJointConvexOnStrictPositive_of_perspectiveTraceRepresentation
#check cstarMatrixRelativeEntropyJointConvexOnStrictPositive_all
#check liebTraceConcavityTarget_all
#check FiniteProbability.expectationReal_trace_normed_exp_add_le
#check sqMagSampleProbability
#check sqMagTraceProbability_expectationComplex_step_eq
#check sqMagTraceProbability_expectationCStarMatrix_step_eq
#check sqMagTraceProbability_expectationCStarMatrix_step_eq_sampleExpectation
#check sqMagTraceProbability_expectationReal_trace_normed_exp_add_step_le
#check sqMagTraceProbMass_snoc
#check sqMagTraceProbability_expectationReal_succ_last_eq
#check cstarMatrix_finset_sum_isSelfAdjoint
#check sqMagTraceProbability_expectationReal_trace_normed_exp_add_sum_le
#check sqMagTraceProbabilityFiniteRealTraceMGFLogBound
#check sqMagTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_add_sum_le
#check rectSelfAdjointDilation_elementwiseSampleResidualIncrement_smul_symmetric
#check sqMagTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_sum_rectSelfAdjointDilation_sampleResidualIncrement_le
#check sqMagTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_rectSelfAdjointDilation_elementwiseTraceResidual_le
#check sqMagTraceProbability_eventProb_exists_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_elementwiseTraceResidual_ge_le
#check sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_elementwiseTraceResidual_lt_ge
#check matrix_trace_kronecker
#check matrix_trace_kronecker_left_identity
#check matrix_trace_kronecker_right_identity
#check cstarMatrixLeftMul
#check cstarMatrixRightMul
#check cstarMatrixLeftMul_mul
#check cstarMatrixRightMul_mul
#check cstarMatrixLeftMul_pow
#check cstarMatrixRightMul_pow
#check cstarMatrixLeftMul_real_smul_add
#check cstarMatrixRightMul_real_smul_add
#check cstarMatrixLeftRightMul_commute
#check cstarMatrixLeftMul_isUnit_of_isStrictlyPositive
#check cstarMatrixRightMul_isUnit_of_isStrictlyPositive
#check cstarMatrixLeftRightRatio
#check cstarMatrixLeftRightRatio_apply
#check cstarMatrixLeftRightRatio_apply_unit
#check cstarMatrixLeftRightRatio_apply_of_unit_eq
#check cstarMatrixLeftRightRatio_apply_of_isStrictlyPositive
#check cstarMatrixEntropyVariationalObjective
#check cstarMatrixEntropyVariationalObjective_liebOptimizer
#check cstarMatrixRelativeEntropyJointConvexOnStrictPositive
#check cstarMatrixRelativeEntropyTraceRepresentationBySuperoperator
#check cstarMatrixRelativeEntropyTraceRepresentationBySuperoperator_all
#check cstarMatrixRelativeEntropyNonnegOnStrictPositive
#check cstarMatrixEntropyTraceFirstOrderConvexityOnStrictPositive
#check cstarMatrixRelativeEntropyNonnegOnStrictPositive_of_entropyTraceFirstOrder
#check cstarMatrixEntropyTraceFirstOrderConvexityOnStrictPositive_of_relativeEntropy_nonneg
#check cstarMatrixEntropyTraceFirstOrderConvexityOnStrictPositive_iff_relativeEntropy_nonneg
#check matrixTrace_diagonal_mul_mul_diagonal_mul_star
#check matrixTrace_sum_diagonal_mul_mul_diagonal_mul_star_re
#check matrixTrace_sum_hermitianCfc_mul_cfc_re
#check matrixTrace_sum_hermitianCfc_mul_cfc_nonneg_of_kernel_nonneg
#check matrixTrace_sum_hermitianCfc_mul_cfc_nonneg_of_eigen_kernel_nonneg
#check matrixTrace_hermitianCfc_firstOrderKernel_sum_nonneg
#check matrixTrace_hermitianCfc_firstOrderKernel_sum_nonneg_of_eigen
#check realEntropy_firstOrderKernel_nonneg
#check matrixTrace_hermitianCfc_entropy_firstOrder_sum_nonneg
#check matrix_isHermitian_cfc_const_one
#check matrix_isHermitian_cfc_const_neg_one
#check matrix_isHermitian_cfc_neg_id
#check matrix_isHermitian_cfc_id
#check matrix_isHermitian_cfc_congr_eigen
#check matrix_isHermitian_cfc_mul
#check matrix_isHermitian_cfc_fun_pow_nat
#check matrix_isHermitian_cfc_inv_of_posDef
#check matrix_posDef_mul_inv_pow_eq_cfc
#check matrix_isHermitian_cfc_entropy
#check matrix_isHermitian_cfc_xlog
#check matrix_isHermitian_cfc_log_mul_id
#check matrixTrace_hermitianCfc_relativeEntropy_re_eq_sum
#check matrixTrace_pow_mul_inv_pow_re_eq_sum
#check matrixPolynomialTraceRatio_re_eq_sum
#check matrixTrace_hermitianCfc_entropy_firstOrder_compact_nonneg
#check cstarMatrix_nonneg_to_matrix_posSemidef
#check cstarMatrix_isStrictlyPositive_to_matrix_posDef
#check cstarMatrixEntropyTraceFirstOrderConvexityOnStrictPositive_of_hermitianCfc
#check cstarMatrixRelativeEntropyNonnegOnStrictPositive_of_hermitianCfc
#check cstarMatrixEntropyVariationalFormula
#check cstarMatrixEntropyVariationalFormula_of_relativeEntropy_nonneg
#check cstarMatrixEntropyVariationalFormula_of_hermitianCfc
#check liebTraceConcavityTarget_of_relativeEntropy_route
#check liebTraceConcavityTarget_of_relativeEntropy_jointConvex
#check finitePSD_iff_finiteHermitianEigenvalues_nonneg
#check finiteLoewnerLe_iff_sub_finiteHermitianEigenvalues_nonneg
#check smulFiniteIdMatrix_symmetric
#check finiteScalarUpperDiff_symmetric
#check finiteScalarUpperDiffEigenvalues
#check finiteLoewnerLe_smul_id_iff_finiteScalarUpperDiffEigenvalues_nonneg
#check finiteLoewnerLe_smul_id_iff_sub_finiteHermitianEigenvalues_nonneg
#check abs_finiteQuadraticForm_le_of_finiteOpNorm2Le
#check finiteQuadraticForm_le_of_finiteOpNorm2Le
#check finiteLoewnerLe_smul_id_of_finiteOpNorm2Le
#check finiteLoewnerLe_neg_smul_id_of_finiteOpNorm2Le
#check algorithm1ExactFrobEvent
#check algorithm1ExactFrobEvent_subset_exactSpectralEvent
#check probability_algorithm1_exact_spectral_of_frob
#check fl_elementwiseTraceResidual_vecNorm2_le_of_exact_fixed_vector
#check sqMagTraceProbMass_marginal_two_ne
#check sqMagTraceProbability_eventProb_sampleHits_pair_ne
#check hitCountPairwiseCenteredMoment_le_steps_mul
#check sqMagTraceProbability_expectationReal_elementwiseTraceResidual_entry_sq_le
#check sqMagTraceProbability_expectationReal_elementwiseTraceResidual_frob_sq_le
#check sqMagTraceProbability_expectationReal_vecNorm2Sq_rectMatMulVec_elementwiseTraceResidual_le
#check sqMagTraceProbability_eventProb_vecNorm2_rectMatMulVec_elementwiseTraceResidual_le_ge_one_sub
#check sqMagTraceProbability_eventProb_fl_vecNorm2_rectMatMulVec_elementwiseTraceResidual_le_ge_one_sub
#check sqMagTraceProbability_eventProb_forall_vecNorm2_rectMatMulVec_elementwiseTraceResidual_le_ge_one_sub_sum
#check sqMagTraceProbability_eventProb_forall_fl_vecNorm2_rectMatMulVec_elementwiseTraceResidual_le_ge_one_sub_sum
#check realUnitIntervalCover
#check rectUnitBallCover_product_grid
#check fintype_card_product_grid_index
#check sqMagTraceProbability_eventProb_algorithm1ExactFrobEvent_ge_one_sub
#check sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_ge_one_sub_frob
#check algorithm1ExactEntrywiseEvent
#check sqMagTraceProbability_eventProb_elementwiseTraceResidual_entry_abs_le_ge_one_sub
#check sqMagTraceProbability_eventProb_algorithm1ExactEntrywiseEvent_ge_one_sub
#check algorithm1ExactEntrywiseEvent_subset_exactSpectralEvent_const
#check probability_algorithm1_exact_spectral_of_entrywise_const
#check sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_ge_one_sub_entrywise
#check sqMagTraceProbability_expectationReal_step_eq
#check exp_sum_stepFunction_eq_prod
#check sqMagTraceProbMass_exp_sum_stepFunction_eq
#check sqMagTraceProbability_expectationReal_exp_sum_stepFunction_eq
#check sqMagTraceProbability_eventProb_sum_stepFunction_ge_le_exp_mul_mgf
#check sqMagTraceProbability_eventProb_sum_stepFunction_le_ge_one_sub_exp_mul_mgf
#check sqMagTraceProbability_eventProb_sum_stepFunction_ge_le_exp_of_one_step_mgf_bound
#check sqMagTraceProbability_eventProb_sum_stepFunction_le_ge_one_sub_exp_of_one_step_mgf_bound
#check sqMagTraceProbability_eventProb_forall_sum_stepFunction_le_ge_one_sub_sum_exp_of_one_step_mgf_bound
#check sqMagProb_sum_exp_stepFunction_le_exp_of_forall_le
#check sqMagProb_sum_exp_stepFunction_le_exp_of_support_forall_le
#check sqMagTraceProbability_eventProb_forall_sum_stepFunction_le_ge_one_sub_sum_exp_of_pointwise_bound
#check sqMagTraceProbability_eventProb_forall_sum_stepFunction_le_ge_one_sub_sum_exp_of_support_pointwise_bound
#check finiteQuadraticForm_rectSelfAdjointDilation_elementwiseTraceResidual_eq_sum_sampleResidualIncrement
#check sqMagTraceProbability_eventProb_forall_finiteQuadraticForm_rectSelfAdjointDilation_elementwiseTraceResidual_le_ge_one_sub_sum_exp_of_one_step_mgf_bound
#check sqMagTraceProbability_eventProb_forall_finiteQuadraticForm_rectSelfAdjointDilation_elementwiseTraceResidual_le_ge_one_sub_sum_exp_of_pointwise_bound
#check sqMagTraceProbability_eventProb_forall_finiteQuadraticForm_rectSelfAdjointDilation_elementwiseTraceResidual_le_ge_one_sub_sum_exp_of_support_pointwise_bound
#check sqMagTraceProbability_expectationReal_rectSelfAdjointDilation_sampleResidualIncrement_eq_zero
#check sqMagTraceProbability_expectationReal_rectSelfAdjointDilation_elementwiseTraceResidual_eq_zero
#check sqMagTraceProbability_expectationReal_finiteQuadraticForm_rectSelfAdjointDilation_sampleResidualIncrement_square_le
#check sqMagTraceProbability_expectationReal_sum_finiteQuadraticForm_rectSelfAdjointDilation_sampleResidualIncrement_square_le
#check sqMagTraceProbability_sum_expectationReal_rectSelfAdjointDilation_square_loewnerLe_scalar_id
#check sqMagTraceProbability_sum_expectationReal_rectSelfAdjointDilation_square_psd
#check algorithm1ExactDilationUpperEvent
#check algorithm1ExactDilationEigenUpperEvent
#check algorithm1ExactDilationEigenUpperIndexEvent
#check algorithm1ExactDilationUpperEvent_subset_exactSpectralEvent
#check algorithm1ExactDilationEigenUpperEvent_subset_exactDilationUpperEvent
#check algorithm1ExactDilationEigenUpperEvent_subset_exactSpectralEvent
#check probability_algorithm1_exact_spectral_of_dilation_upper
#check probability_algorithm1_exact_spectral_of_dilation_eigen_upper
#check probability_algorithm1_exact_dilation_eigen_upper_of_index_bounds
#check probability_algorithm1_exact_spectral_of_dilation_eigen_upper_index_bounds
#check probability_algorithm1_fl_spectral_of_exact_dilation_upper
#check probability_algorithm1_fl_spectral_of_exact_dilation_eigen_upper
#check probability_algorithm1_fl_spectral_of_exact_dilation_eigen_upper_index_bounds
#check elementwiseTruncate
#check elementwiseTracePositiveProb
#check sqMagTraceProbability_eventProb_elementwiseTracePositiveProb
#check elementwiseTruncate_abs_le
#check frobNormSqRect_elementwiseTruncate_le
#check frobNormRect_elementwiseTruncate_le
#check elementwiseTruncate_square_error_frobNormRect_le_half
#check elementwiseTruncate_square_error_rectOpNorm2Le_half
#check elementwiseTruncatedTraceResidual_rectOpNorm2Le_of_truncated
#check elementwiseTruncatedTraceResidual_square_rectOpNorm2Le_of_half
#check algorithm1ExactTruncatedSpectralEvent
#check probability_algorithm1_exact_truncated_spectral_of_sampled_half
#check frobNormRect_elementwiseSampleContribution_truncated_le
#check frobNormRect_elementwiseSampleResidualIncrement_truncated_le
#check rectOpNorm2Le_elementwiseSampleResidualIncrement_truncated
#check sqMagTraceProbability_eventProb_truncatedResidualIncrementsBoundedEvent_eq_one
#check finiteOpNorm2Le_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated
#check finiteQuadraticForm_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated_le
#check sqMagTraceProbability_eventProb_truncatedDilationIncrementsBoundedEvent_eq_one
#check finiteLoewnerLe_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated
#check finiteLoewnerLe_neg_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated
#check truncatedDilationIncrementLoewnerBoundedEvent
#check sqMagTraceProbability_eventProb_truncatedDilationIncrementLoewnerBoundedEvent_eq_one
#check truncatedDilationIncrementLoewnerBoundedEvent_subset_exactDilationUpperEvent_sum_bound
#check sqMagTraceProbability_eventProb_algorithm1ExactDilationUpperEvent_truncated_sum_bound_eq_one
#check sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncated_sum_bound_eq_one
#check finiteLoewnerLe_rectSelfAdjointDilation_square_elementwiseSampleResidualIncrement_truncated
#check sqMagTraceProbability_eventProb_truncatedDilationIncrementSquaresBoundedEvent_eq_one
#check truncatedDilationBernsteinBoundedEvent
#check sqMagTraceProbability_eventProb_truncatedDilationBernsteinBoundedEvent_eq_one
#check sqMagTraceProbability_eventProb_forall_finiteQuadraticForm_rectSelfAdjointDilation_truncatedTraceResidual_le_ge_one_sub_sum_exp_of_support_bound
#check fl_elementwiseTraceResidual_rectOpNorm2Le_of_exact
#check fl_elementwiseTruncatedTraceResidual_rectOpNorm2Le_of_truncated
#check algorithm1FlTruncatedSpectralEvent
#check probability_algorithm1_fl_truncated_spectral_of_sampled_half
#check fl_elementwiseTraceResidual_rectOpNorm2Le_of_exact_and_hitCount_le
#check probability_algorithm1_fl_spectral_of_exact_spectral
#check probability_algorithm1_fl_spectral_of_exact_frob
#check sqMagTraceProbability_eventProb_algorithm1FlSpectralEvent_ge_one_sub_frob
#check sqMagTraceProbability_eventProb_algorithm1FlSpectralEvent_ge_one_sub_entrywise
#check highProbability_sqMagTraceStability_of_markov_budget
#check highProbability_sqMagTraceStability_of_pairwise_chebyshev_budget
#check highProbability_sqMagTraceStability_of_independent_chernoff_budget
#check highProbability_sqMagTraceStability_of_independent_chernoff_optimized_tail_budget
```

The Algorithm 1 theorem surface is summarized by the checked declarations above
and indexed in [`docs/LIBRARY_LOOKUP.md`](docs/LIBRARY_LOOKUP.md).

Algorithm 2 row sampling is also formalized for the equation (4) distribution
`p_i = ||A_i*||_2^2 / ||A||_F^2`. The row-sampling API proves the literal
sampled-sketch entrywise floating-point stability bound, elementwise
unbiasedness of `ÃᵀÃ`, the squared-Frobenius second moment, and the expectation
bound plus the high-probability Markov form of equation (5):
`Pr[||ÃᵀÃ - AᵀA||_F ≤ ε ||A||_F²] ≥ 1 - 1/(s ε²)`. Since Algorithm 2 returns
sampled rows rather than accumulating repeated samples, no hit-count or
Chernoff stability bound is involved in this floating-point result. The
floating-point layer is tracked as an explicit perturbation. By current project
convention, the row probabilities are exact; no FP error is charged for
probability construction. The implementation-facing row-sampling surface
still exposes `ComputedRowScaleDen` for computed `sqrt(s * p_i)` denominators,
so square-root denominator computation and final rounded division remain
visible while the canonical equation (5) concentration theorems stay statements
about the exact row-norm product law.
For the theoretical
Gram matrix formed exactly after rounded row scaling, the scaling-only theorem
adds just the row-rescaling division budget
`n * ((2 * fp.u + fp.u ^ 2) * ||A||_F²)`; this is also recorded under the
explicit `tau_dot = 0` specialization
`rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_tau_dot_zero`.
This theorem is about `fl_rowSampleGram`, the exact mathematical Gram matrix of
the rounded sampled rows; it is separate from the optional computed-Gram theorem
for `fl_rowSampleGramDot`.
The fully computed Gram theorem
reuses the library's `fl_dotProduct` and `dotProduct_error_bound`, then
combines row-rescaling division error with dot-product evaluation error through
the deterministic budget
`rowSampleGramFullFpPerturbBudget fp s A`:
`Pr[||fl_dot(Ã)ᵀfl_dot(Ã) - AᵀA||_F ≤ ε ||A||_F² + rowSampleGramFullFpPerturbBudget fp s A] ≥ 1 - 1/(s ε²)`.
The row-scaling and dot-product budget definitions depend on the number `n` of
columns implicitly through the type `A : Fin m → Fin n → ℝ`; the library also
proves closed-form lemmas exposing this `n` factor:
`rowSampleGramFpPerturbBudget_eq_nat_mul` and
`rowSampleGramDotProductBudget_eq_nat_mul`.
This theorem proves internally that zero-probability row traces have zero mass,
so the floating-point division model is applied only on the positive-probability
support of the sampler.
The library also keeps the more general union-bound transfer lemma with a
separate high-probability perturbation event `1 - δτ`, for future use if a
sharper probabilistic rounding perturbation theorem is proved.

The leverage-score specialization of Algorithm 2 is formalized for equation
(6). For an orthonormal-column matrix `U`, the library proves
`p_i = ||U_i*||_2^2 / n`, `UᵀU = I`, and the equation (7) subspace-embedding
bound in vector-action operator-2 form:
`Pr[∀x, ||(ŨᵀŨ - I)x||_2 ≤ ε ||x||_2] ≥ 1 - 1/(s (ε/n)^2)`.
By the same exact-probability convention, the leverage probabilities in
equation (6) are treated as exact sampling laws. Floating-point errors for
computed bases, square-root denominators, row scaling, and optional dot products
remain in scope when a concrete implementation computes those quantities.
The fully floating-point corollary reuses the previous row-sampling stability
budget and the dot-product theorem:
`Pr[∀x, ||(fl_dot(Ũ)ᵀfl_dot(Ũ) - I)x||_2 ≤ (ε + rowSampleGramFullFpPerturbBudget fp s U) ||x||_2] ≥ 1 - 1/(s (ε/n)^2)`.
The formal statement uses `opNorm2Le`, the vector-action form of the usual
operator-2-norm upper-bound statement, avoiding a separate supremum-valued
spectral norm object.
For the sharper Bennett finite-Loewner route, the current implementation-facing
endpoint is
`leverageTraceProbability_eventProb_fl_rowSampleGramDotWithFlMulThenSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget`;
it instantiates the concrete leverage denominator
`fl_sqrt(fl_mul s p_i)` through `leverageFlMulThenSqrtRowScaleDen`, rather than
leaving an arbitrary computed-denominator certificate in the final theorem
surface.
The actual-input equation (7) endpoint is also formalized. Given exact analysis
witnesses `U`, `C`, and `A = U C` with `UᵀU = I`, the theorem
`leverageTraceProbability_eventProb_factoredInput_fl_rowSampleGramDotWithFlMulThenSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget`
transfers the exact leverage event to `AᵀA` by right-Gram congruence and then
charges the computed path that samples rows of `A`, forms
`fl_sqrt(fl_mul s p_i)`, rounds sampled-row divisions, and rounds the
length-`s` Gram dot products. The theorem does not claim that `U` or `C` were
computed by QR, SVD, or a rank-revealing routine; such generation routines
remain separate computed-quantity certificates.

For the sharper source route to equation (7), the library now proves the
single-sample rank-one facts needed by the Oliveira/Tropp matrix-concentration
argument: each leverage outer-product estimator is PSD, its expectation is
`I_n`, and it is bounded by `n I_n` in finite Loewner order. These facts are
recorded as prerequisites, not as the final sharp concentration theorem. The
row-sampling trace-MGF product-law adapter is also formalized, so future
rank-one concentration work can reuse the no-hidden-Lieb trace-MGF iteration
instead of rebuilding independence machinery. The centered one-sample
leverage covariance log-CGF bound is now also instantiated from the local
generic C-star Bernstein theorem: for `X_i = rowOuterGramSample U i - I`, the
library proves zero mean, self-adjointness, the conservative spectrum bound
`lambda_max(X_i) <= n`, and the Bernstein log-CGF inequality without assuming
the target concentration event. The source-sharp route now also proves the
exact variance identity `E[(Y_i-I)^2]=(n-1)I`, the negative-centered log-CGF
bound for `I-Y_i`, positive and negative row-trace scalar MGF bounds, one-sided
Loewner high-probability tails, a two-sided finite-Loewner event with an
explicit exponential tail budget, a Bennett sample-budget corollary, and a
fully floating-point two-sided Loewner corollary that adds
`rowSampleGramFullFpPerturbBudget fp s U` to the exact radius. The sample-budget
form keeps the upper and lower Bennett denominators explicit:
`2(n-1)+(2/3)nε` for the upper tail and `2(n-1)+(2/3)ε` for the lower tail.

```lean
#check rowSqNormProb
#check fl_rowSampleSketch_error_bound
#check rowSqNormTraceProbability_expectationReal_rowSampleGram_entry
#check rowSqNormTraceProbability_expectationReal_rowSampleGram_frob_error_sq_le
#check rowSqNormTraceProbability_expectationReal_rowSampleGram_frob_error_le
#check rowSqNormTraceProbability_eventProb_rowSampleGram_frob_error_le_epsilon
#check rowSqNormTraceProbability_eventProb_rowSampleGram_frob_error_le_epsilon_of_budget
#check rowSampleGram_entry_error_bound_of_entrywise
#check rowTracePositiveProb
#check rowSqNormTraceProbability_eventProb_rowTracePositiveProb
#check fl_rowSampleGramDot
#check rowSampleGramFpPerturbBudget
#check rowSampleGramDotProductBudget
#check rowSampleGramFullFpPerturbBudget
#check rowSampleGramFpPerturbBudget_eq_nat_mul
#check rowSampleGramDotProductBudget_eq_nat_mul
#check rowSampleGram_perturb_budget_le_explicit
#check rowSketchGram_dot_frob_error_bound_of_entrywise
#check rowSampleGram_dot_product_budget_le_explicit
#check rowSqNormTraceProbability_expectationReal_fl_rowSampleGram_entry_bias_bound_of_entrywise
#check rowSqNormTraceProbability_expectationReal_fl_rowSampleGram_frob_error_le_add_perturb
#check rowSqNormTraceProbability_eventProb_computedGram_frob_error_le_epsilon_add_tau
#check rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_tau
#check rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_tau_of_forall
#check rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_tau_of_entrywise_budget
#check rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_explicit_budget
#check rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_scaling_budget
#check rowSqNormTraceProbability_eventProb_fl_rowSampleGramDot_frob_error_le_epsilon_add_explicit_budget
#check rowSqNormSampleProbability
#check rowSqNormTraceProbability_expectationReal_trace_normed_exp_add_sum_le
#check rowSqNormTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_add_sum_le
#check rowSqNormTraceProbabilityFiniteRealTraceMGFLogBound_zero_le_card_mul_exp_of_log_le_real_smul_one
#check rowSampleGram_sub_finiteIdMatrix_eq_centered_rowOuterGramSample_average
#check HasOrthonormalColumns
#check leverageScoreProb
#check rowGram_eq_id_of_orthonormal_columns
#check rowSqNormProbDen_eq_nat_of_orthonormal_columns
#check rowOuterGramSample_eq_zero_of_prob_zero
#check finiteQuadraticForm_rowOuterGramSample_eq_sq_div
#check finitePSD_rowOuterGramSample
#check leverage_rowOuterGramSample_finitePSD
#check leverage_rowOuterGramSample_mean_eq_id
#check leverage_rowOuterGramSample_finiteLoewnerLe_nat
#check leverage_rowOuterGramSample_centered_expectationCStarMatrix_eq_zero
#check leverage_rowOuterGramSample_centered_spectrum_le_nat
#check leverage_rowOuterGramSample_centered_square_expectationCStarMatrix_eq
#check leverage_rowOuterGramSample_centered_log_cgf_le
#check leverage_rowOuterGramSample_centered_log_cgf_le_scalar
#check leverage_rowOuterGramSample_neg_centered_log_cgf_le
#check leverage_rowOuterGramSample_neg_centered_log_cgf_le_scalar
#check leverage_rowSqNormTraceProbabilityFiniteRealTraceMGFLogBound_centered_le
#check leverage_rowSqNormTraceProbabilityFiniteRealTraceMGFLogBound_neg_centered_le
#check leverage_rowSqNormTraceProbability_eventProb_forall_finiteHermitianEigenvalue_centered_sum_lt_ge_one_sub_exp
#check leverageTraceProbability_eventProb_rowSampleGram_finiteLoewnerLe_upper_lt_ge_one_sub_exp
#check leverageTraceProbability_eventProb_rowSampleGram_finiteLoewnerLe_lower_lt_ge_one_sub_exp
#check leverageTraceProbability_eventProb_rowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_exp
#check leverageTraceProbability_eventProb_rowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_tail_budget
#check leverageTraceProbability_eventProb_rowSampleGram_finiteLoewnerLe_upper_ge_one_sub_delta_half_of_sample_budget
#check leverageTraceProbability_eventProb_rowSampleGram_finiteLoewnerLe_lower_ge_one_sub_delta_half_of_sample_budget
#check leverageTraceProbability_eventProb_rowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
#check leverageTraceProbability_eventProb_rowSampleGram_opNorm2_error_le_epsilon
#check leverage_fl_rowSampleGramDot_perturb_bound
#check leverageTraceProbability_eventProb_fl_rowSampleGramDot_opNorm2_error_le_epsilon_add_budget
#check leverageTraceProbability_eventProb_fl_rowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
```

The Algorithm 2 theorem and corollary surface is summarized by the checked
declarations above and indexed in [`docs/LIBRARY_LOOKUP.md`](docs/LIBRARY_LOOKUP.md).

## RandNLA Algorithm 3

Algorithm 3 from Drineas and Mahoney's CACM survey is the random-projection
preconditioning meta-algorithm. Given preprocessing matrices, it returns one of
`PiL * A`, `A * PiR`, or `PiL * A * PiR` to uniformize rows, columns, or
entries before a later sampling algorithm is applied.

The formalization is deterministic after the random preprocessing matrices have
been drawn. It defines the exact branches and their floating-point analogues,
reuses the existing `fl_matMul` implementation, proves Frobenius-norm
preservation for square orthogonal preprocessors, proves that square orthogonal
row/column/two-sided preprocessing preserves an orthonormal-column basis and
hence the equation (6) leverage denominator, and proves the deterministic
SRHT-style sign/orthogonal prerequisite used before a Rademacher row-norm
flattening theorem. The implementation-facing Algorithm 3 surface also exposes
computed preprocessing matrices through `ComputedPreconditioner`: stored or
generated transform entries carry entrywise error bounds before the rounded
matrix products are evaluated, and the row/column total bounds separate
transform-entry error from matrix-multiplication rounding.
For the finite rectangular-isometry signed-mixing branch, the implementation
surface now has both an exact-basis endpoint and an actual-input endpoint. The
actual-input theorem uses exact analysis witnesses `A = U C` with
`U^T U = I`, transfers the exact signed-mixing sample-Gram event to
`rowGram A` by right-Gram congruence, and then charges the computed path
`Pihat = fl(G * diag(sign))`, `Yhat = fl(Pihat * A)`, the concrete uniform
row-scale denominator
`uniformRowFlSqrtMulInvSqrtScaleDen`, rounded sampled-row divisions, and
rounded Gram dot products. The final concrete-denominator theorems are
`signedMixingUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform`,
`signedMixingUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform`, and
`signedMixingUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_total_budget`.
They have no separate `deltaComp`: exact Rademacher and uniform-row laws are
kept exact, while every non-probability computation on that path is charged.
For SRHT-style preprocessing, `ComputedVector` records the realized sign table,
`ComputedMatrix.diag` embeds it as the computed diagonal factor, and
`ComputedPreconditioner.flSignedHadamard` packages the rounded product
`fl(Hhat * diag(signhat))` as a computed preconditioner for the ideal
`H * diag(sign)`.  The Rademacher law remains exact; this certificate only
charges storage/roundoff in the realized transform object.
`ComputedPreconditioner.flSignedHadamardExactFactors` specializes this path to
exact supplied Hadamard/sign factors while still charging the rounded product
that forms the realized preconditioner.  The remaining SRHT generator
obligation is a concrete fast FHT recurrence/apply routine or a sign-storage
format not represented by the modeled rounded-copy certificates
`fl_mul sign_i 1`, `fl_add sign_i 0`, and `fl_sub sign_i 0`.
`ComputedMatrix.flSqrtInvNatScaledPattern` closes the rounded scale-table
subcase for a supplied sign pattern: it charges the rounded
`fl_sqrt ((m : R)^-1)` scale while keeping the sign-pattern entries and
Rademacher law exact, and `hadamardFlat_sqrt_inv_nat_mul_signPattern` proves
that the corresponding ideal table satisfies `HadamardFlat`.
`sylvesterHadamardSignPattern` closes the concrete generated sign-pattern
subcase for dimensions `2^p`: the table is generated by exact bit-parity logic,
`sylvesterHadamardSignPattern_isSignPattern` proves every entry squares to one,
and `ComputedMatrix.flSqrtInvNatScaledSylvesterPattern` charges the rounded
scale table for that generated pattern.  A fast in-place FHT recurrence/apply
routine still needs its own arithmetic certificate.
`ComputedPreconditioner.flSignedHadamardScaledPattern` and
`signedHadamardScaledPatternPreconditioner` plug that rounded scaled-pattern
table into the signed-Hadamard product certificate, and
`signedHadamardUniformRowTraceProbability_eventProb_scaledPatternComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one`
shows the computed-left `Vhat` perturbation event holds with probability one
under the exact Rademacher/uniform-row law.
`ComputedVector.flStoredSign`,
`ComputedPreconditioner.flSignedHadamardScaledPatternStoredSign`, and
`signedHadamardScaledPatternStoredSignPreconditioner` close the rounded-copy
sign-storage variant: storing an exact Rademacher sign by `fl_mul sign_i 1`
adds an entry radius `u`, and
`signedHadamardUniformRowTraceProbability_eventProb_scaledPatternStoredSignComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one`
feeds that stored-sign certificate into the same probability-one computed-left
event.
`ComputedVector.flStoredSignAddZeroRight`,
`ComputedPreconditioner.flSignedHadamardScaledPatternStoredSignAddZeroRight`,
and `signedHadamardScaledPatternStoredSignAddZeroRightPreconditioner` close the
add-zero copy variant: storing an exact Rademacher sign by `fl_add sign_i 0`
also adds an entry radius `u`, and
`signedHadamardUniformRowTraceProbability_eventProb_scaledPatternStoredSignAddZeroRightComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one`
feeds that alternative stored-sign certificate into the same exact-law
probability-one event.
`ComputedVector.flStoredSignSubZeroRight`,
`ComputedPreconditioner.flSignedHadamardScaledPatternStoredSignSubZeroRight`,
and `signedHadamardScaledPatternStoredSignSubZeroRightPreconditioner` close the
subtract-zero copy variant: storing an exact Rademacher sign by
`fl_sub sign_i 0` also adds an entry radius `u`, and
`signedHadamardUniformRowTraceProbability_eventProb_scaledPatternStoredSignSubZeroRightComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one`
feeds this third stored-sign certificate into the same exact-law
probability-one event.
`ComputedPreconditioner.flSignedHadamardSylvesterPattern`,
`ComputedPreconditioner.flSignedHadamardSylvesterPatternStoredSign`, and
`ComputedPreconditioner.flSignedHadamardSylvesterPatternStoredSignAddZeroRight`,
and `ComputedPreconditioner.flSignedHadamardSylvesterPatternStoredSignSubZeroRight`
specialize the rounded signed-Hadamard certificates to the generated
Sylvester/Walsh table, and the matching `signedHadamard...sylvesterPattern...`
event theorems, including the subtract-zero stored-sign variant, feed those
generated-pattern certificates into the same probability-one computed-left
`Vhat` perturbation event.
`fhtButterflyExact`, `flFhtButterfly`,
`flFhtButterfly_add_error_bound`, and `flFhtButterfly_sub_error_bound` close
the scalar arithmetic primitive for one fast-Hadamard butterfly: the two
computed outputs `fl_add a b` and `fl_sub a b` are compared to the exact
outputs `a + b` and `a - b` with relative radii `u`.
`fhtPairUpdateExact`, `flFhtPairUpdate`, `fhtPairUpdateErrorBudget`, and
`flFhtPairUpdate_error_bound` lift that primitive to one vector pair update,
with an entrywise budget for the two modified coordinates and zero budget for
unchanged exact-reference coordinates.  This is still only the local pair
certificate.  `fhtPairUpdatePropagatedErrorBudget` and
`flFhtPairUpdate_propagated_error_bound` additionally handle the staged-FHT
case where the input vector is already approximate: if
`|xhat_i - x_i| <= E_i`, the modified coordinates get budgets
`u |xhat_p + xhat_q| + E_p + E_q` and
`u |xhat_p - xhat_q| + E_p + E_q`, while untouched coordinates keep their
previous `E_i` budget.  `fhtPairScheduleExact`, `flFhtPairSchedule`,
`fhtPairSchedulePropagatedErrorBudget`, and
`flFhtPairSchedule_propagated_error_bound` compose this propagated budget across
an arbitrary ordered list of FHT pair updates.  `fhtScaledPairScheduleExact`,
`flFhtScaledPairSchedule`, `fhtScaledPairScheduleErrorBudget`, and
`flFhtScaledPairSchedule_error_bound` then add a computed final scale `chat`
with certificate `|chat - c| <= eta`: the final entry budget is
`u |chat * yhat_i| + |chat| * Es_i + eta * (|yhat_i| + Es_i)`, charging the
rounded scale multiplication, propagated schedule error, and scale-generation
error.  `fhtScaledPairScheduleMatrixExact`,
`flFhtScaledPairScheduleMatrix`,
`fhtScaledPairScheduleMatrixErrorBudget`,
`flFhtScaledPairScheduleMatrix_error_bound`, and
`ComputedMatrix.flScaledFhtPairScheduleColumns` lift the same certificate
columnwise to a computed matrix, so a supplied schedule can feed downstream
`ComputedMatrix`/`ComputedPreconditioner` surfaces.  `fhtSqrtInvNatScale`,
`flFhtSqrtInvNatScale`, `fhtSqrtInvNatScaleErrorRadius`,
`flFhtSqrtInvNatScale_error_bound`,
`flFhtScaledPairSchedule_sqrtInvNatScale_error_bound`,
`flFhtScaledPairScheduleMatrix_sqrtInvNatScale_error_bound`, and
`ComputedMatrix.flScaledFhtPairScheduleColumnsSqrtInvNat` instantiate the
normalization scale with the concrete rounded routine `fl_sqrt ((m : R)^-1)`.
The exact schedule-generation layer now starts with `fhtStagePairPredicate`,
`fhtStagePairs`, `mem_fhtStagePairs_iff`, the stride/second-index/modulus and
non-self-pair facts, the same-first/same-second partner uniqueness lemmas
`fhtStagePairs_snd_eq_of_fst_eq` and `fhtStagePairs_fst_eq_of_snd_eq`, and the
lower/upper-half separation lemma
`fhtStagePairs_fst_ne_snd_of_mem_mem` backed by
`nat_stride_add_mod_two_stride_ge_of_mod_lt`, plus the reverse separation
`fhtStagePairs_snd_ne_fst_of_mem_mem` and the same-first/same-second pair
identity theorems `fhtStagePairs_eq_of_fst_eq` and
`fhtStagePairs_eq_of_snd_eq`.  The generic exact-update order bridge
`fhtPairUpdateExact_commute_of_disjoint` and the stage specializations
`fhtStagePairs_disjoint_of_ne` and
`fhtStagePairs_pairUpdateExact_commute_of_ne` prove that distinct generated
butterflies in one stage have no shared coordinates and commute.  The list-level
bridges `fhtPairScheduleExact_commute_update_of_forall` and
`fhtStagePairs_pairUpdateExact_commute_schedule_of_ne` move such an update
across a whole exact schedule list whose members are generated in the same
stage and distinct from it.  The rounded functional schedule now has the same
same-stage no-alias/order certificate through
`flFhtPairUpdate_commute_of_disjoint`,
`flFhtPairSchedule_commute_update_of_forall`,
`fhtStagePairs_flFhtPairUpdate_commute_of_ne`, and
`fhtStagePairs_flFhtPairUpdate_commute_schedule_of_ne`.  The no-duplicate and
no-touch/output bridge
theorems `fhtStagePairs_nodup`,
`fhtPairScheduleExact_apply_of_forall_not_mem`,
`fhtPairScheduleExact_apply_pair_of_mem_stage_list`, and
`fhtStagePairs_pairScheduleExact_apply_pair_of_mem` now prove the exact
one-stage formula: for every generated pair `(a,b)`, the full ordered stage
schedule returns `x_a + x_b` at `a` and `x_a - x_b` at `b`.  It then
specializes to
`fhtSylvesterStagePairs` with `mem_fhtSylvesterStagePairs_iff` for dimension
`2^p` and stride `2^stage`, with direct wrappers
`fhtSylvesterStageScheduleExact_apply_pair_of_mem`,
`fhtSylvesterStageScheduleExact_apply_fst_of_mem`, and
`fhtSylvesterStageScheduleExact_apply_snd_of_mem`.  The coordinate constructors
`fhtStagePairs_mem_lower_mk`, `fhtSylvesterStagePairs_mem_lower_mk`, and
`fhtSylvesterStagePairs_mem_upper_mk`, together with
`fhtSylvesterStageScheduleExact_apply_lower_mk` and
`fhtSylvesterStageScheduleExact_apply_upper_mk`, turn those pair-list formulas
into lower/upper coordinate formulas with explicit partner and modulus
hypotheses.  The power-of-two coverage layer
`nat_add_stride_lt_of_mod_lt_of_dvd`,
`nat_sub_stride_mod_two_stride_lt_of_mod_ge`,
`two_mul_two_pow_dvd_two_pow_of_lt`,
`fhtSylvesterStage_lower_partner_lt_of_mod_lt`,
`fhtSylvesterStage_upper_value_le_of_mod_ge`, and
`fhtSylvesterStage_upper_partner_mod_lt_of_mod_ge` now derives those bound and
partner-modulus hypotheses from the lower/upper block test itself.  Consequently
`fhtSylvesterStageScheduleExact_apply_lower_of_mod_lt` and
`fhtSylvesterStageScheduleExact_apply_upper_of_mod_ge` give the one-stage
coordinate formulas needed by the parity-table induction under only the visible
block test.  The bit-test bridge
`nat_testBit_eq_false_of_mod_two_mul_two_pow_lt`,
`nat_testBit_eq_true_of_two_pow_le_mod_two_mul_two_pow`,
`fhtSylvesterStage_testBit_eq_false_of_mod_lt`, and
`fhtSylvesterStage_testBit_eq_true_of_mod_ge` further identifies those lower
and upper block tests with the stage bit of the coordinate index.  The partner
wrappers `fhtSylvesterStage_upper_partner_testBit_eq_true_of_mod_lt` and
`fhtSylvesterStage_lower_partner_testBit_eq_false_of_mod_ge` record the
corresponding stage-bit facts for the generated upper and lower partners, and
`fhtSylvesterStage_upper_partner_testBit_eq_of_ne_of_mod_lt` plus
`fhtSylvesterStage_lower_partner_testBit_eq_of_ne_of_mod_ge` prove that those
partners agree with the original coordinate in every non-stage bit.
The parity-count sign adapters
`sylvesterHadamardSignPattern_eq_or_neg_of_parityWeight_eq_add_bool`,
`sylvesterHadamardSignPattern_eq_of_parityWeight_eq`, and
`sylvesterHadamardSignPattern_neg_of_parityWeight_eq_add_one` now convert a
future partner-row parity-count identity into the exact same-sign/negated-sign
Sylvester/Walsh recurrence.  The finite-sum bit-toggle adapter
`sylvesterHadamardParityWeight_partner_eq_add_stage_of_bits`, together with
`sylvesterHadamardSignPattern_partner_eq_or_neg_of_stage_bit`, closes the
abstract case where two row indices agree in every non-stage bit and toggle the
stage bit from cleared to set.  The concrete generated-partner instantiations
`sylvesterHadamardParityWeight_upper_partner_eq_add_stage_of_mod_lt`,
`sylvesterHadamardSignPattern_upper_partner_eq_or_neg_of_mod_lt`,
`sylvesterHadamardParityWeight_upper_eq_lower_partner_add_stage_of_mod_ge`, and
`sylvesterHadamardSignPattern_upper_eq_or_neg_lower_partner_of_mod_ge` close
the lower/upper block cases for `i + 2^stage` and `i - 2^stage`.  The remaining
stage-list append and range-succ recurrences
`fhtSylvesterStageScheduleListExact_append`,
`flFhtSylvesterStageScheduleList_append`,
`fhtSylvesterStageScheduleListPropagatedErrorBudget_append`,
`fhtSylvesterStageScheduleListExact_range_succ`,
`flFhtSylvesterStageScheduleList_range_succ`, and
`fhtSylvesterStageScheduleListPropagatedErrorBudget_range_succ` close the
induction hook for applying all previous generated stages followed by the
current stage.  The partial-transform anchors
`sylvesterHadamardPartialParity`, `sylvesterHadamardPartialSignPattern`,
`sylvesterHadamardPartialUnscaledApply`,
`sylvesterHadamardPartialSignPattern_zero`,
`sylvesterHadamardPartialUnscaledApply_zero`,
`sylvesterHadamardPartialSignPattern_full`, and
`sylvesterHadamardPartialUnscaledApply_full` define the induction target:
depth zero is the identity transform, while depth `p` is the full concrete
Sylvester/Walsh bit-parity transform.  The partial-sign recurrences
`sylvesterHadamardPartialSignPattern_succ_eq_or_neg`,
`sylvesterHadamardPartialSignPattern_succ_eq_of_stage_bit_false`, and
`sylvesterHadamardPartialSignPattern_succ_eq_or_neg_of_stage_bit_true`, the
block-split theorems `sylvesterHadamardPartialUnscaledApply_succ_lower` and
`sylvesterHadamardPartialUnscaledApply_succ_upper`, and the stage theorem
`fhtSylvesterStageScheduleExact_partialUnscaledApply_eq_succ` prove the
one-stage recurrence from partial depth `stage` to `stage+1`.  The induction
theorem `fhtSylvesterStageScheduleListExact_range_eq_partialUnscaledApply` and
the final theorem `fhtSylvesterScheduleRealizesSignPattern_generated` prove that
the generated exact FHT schedule realizes the concrete Sylvester/Walsh table.
These are deterministic integer/FHT facts, not sampling-law or
probability-construction results.
The full generated schedule is `fhtSylvesterSchedulePairs`, with membership
facts `mem_fhtSylvesterSchedulePairs_iff` and
`mem_fhtSylvesterSchedulePairs_iff_stage_rule`, plus non-self and strict-order
facts for generated pairs.  `flFhtSylvesterSchedule_propagated_error_bound`,
`flFhtScaledSylvesterScheduleMatrix_sqrtInvNatScale_error_bound`, and
`ComputedMatrix.flScaledFhtSylvesterScheduleColumnsSqrtInvNat_entry_error_bound`
specialize the propagated FP budget and rounded square-root normalization to
that full generated schedule.  The stage-factorization bridge
`fhtSylvesterScheduleExact_eq_stageScheduleListExact`,
`flFhtSylvesterSchedule_eq_stageScheduleList`, and
`fhtSylvesterSchedulePropagatedErrorBudget_eq_stageScheduleList` proves that
the flat generated list and its propagated budget are exactly the stage-by-stage
recurrences over `List.range p`; the append/range-succ stage-list lemmas give
the exact, rounded, and propagated-budget induction recurrence over
`List.range (stage + 1)`.  The transform-correctness theorem
`fhtSylvesterScheduleRealizesSignPattern_generated` closes
`fhtSylvesterScheduleRealizesSignPattern p` for every `p`, and the unconditional
bridges
`fhtScaledSylvesterScheduleMatrixExact_eq_sylvesterHadamardScaledMatrixApply`
and `fhtScaledSylvesterScheduleMatrixExact_signed_eq_preconditionRows` identify
the generated scaled FHT with the exact bit-parity table and the exact `H D U`
preconditioner used in the SRHT analysis.  This closes generated-schedule FP
propagation, stage decomposition, the realization base case, the stage-list
induction spine, the partial-transform base/full-depth anchors, the one-stage
partial recurrence, the final exact transform-correctness induction, and the
exact signed-preconditioner bridge.  A layout-specific FHT apply routine still
has to add rounded storage/overwrite effects if its concrete array behavior
differs from the functional pair-update schedule, but the functional fast
generated-FHT preconditioner path is now wired through
`ComputedPreconditioner.flSignedHadamardSylvesterFhtSchedule`.
That constructor applies the rounded generated schedule to a computed diagonal
sign matrix and uses `fhtScaledSylvesterScheduleMatrixExact_diag_eq_matMul_diag`
to identify the exact reference object with the scaled Sylvester/Walsh
`H D_sign` matrix.  The wrappers
`signedHadamardSylvesterFhtSchedulePreconditioner`,
`signedHadamardSylvesterFhtScheduleStoredSignPreconditioner`,
`signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one`,
and
`signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one`
feed that fast preconditioner into the existing exact-law computed-left event.
The generated Sylvester/Walsh matrix no longer needs to be supplied with an
external orthogonality witness: `isOrthogonal_sqrt_inv_nat_mul_sylvesterSignPattern`
proves the normalized bit-parity table is orthogonal from the concrete sign
definition, using the new column/row inner-product lemmas
`sylvesterHadamardScaled_col_inner` and
`sylvesterHadamardScaled_row_inner`.  The final actual-input SRHT endpoint
`signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess`
sets `A = U C`, instantiates the functional generated-FHT stored-sign
preconditioner, and uses the concrete denominator
`uniformRowFlSqrtMulInvSqrtScaleDen`; the exact Rademacher/uniform laws remain
mathematical, while sign storage, FHT arithmetic, rounded normalization,
`fl(Pihat*A)`, denominator formation, row divisions, and Gram dot products are
charged by the displayed budget.
The stored-input siblings
`signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignStoredInputMulOneComputedLeftInputPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess`
and its add-zero/subtract-zero variants add concrete input-storage paths
`Ahat_ij = fl_mul A_ij 1`, `Ahat_ij = fl_add A_ij 0`, or
`Ahat_ij = fl_sub A_ij 0` before forming `fl(Pihat*Ahat)`.  The factors
`U,C` remain exact analysis witnesses for `A=UC`; the implemented
non-probability matrix used in the product is the stored
`ComputedMatrix.flMulOne fp A`, `ComputedMatrix.flAddZeroRight fp A`, or
`ComputedMatrix.flSubZeroRight fp A`, and its storage radius is propagated
through the computed-left/input budget and the same concrete denominator and
sampled-Gram path.
The modeled all-coordinate add-zero writeback path is now promoted to the same
final actual-input theorem via
`signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignStoredAddZeroRightComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess`;
it adds the `fl_add y_i 0` FHT writeback/copy charge after every pair update
without changing the exact probability laws.
The modified-coordinate add-zero variant is also promoted to a final
actual-input theorem via
`signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignModifiedStoredAddZeroRightComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess`;
it charges the same `fl_add y_i 0` copy only on the two butterfly outputs
modified by each pair update.
The all-coordinate multiply-one and subtract-zero variants are now promoted to
final actual-input theorems as well, via
`signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignStoredMulOneComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess`
and
`signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignStoredSubZeroRightComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess`;
they charge `fl_mul y_i 1` or `fl_sub y_i 0` on every coordinate after every
FHT pair update, with the same exact probability laws and concrete denominator
routine.
The modified-coordinate multiply-one and subtract-zero variants are now also
promoted to final actual-input theorems via
`signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignModifiedStoredMulOneComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess`
and
`signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignModifiedStoredSubZeroRightComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess`;
they charge the same copy operations only on the two butterfly outputs
modified by each pair update.
The concrete modeled writeback/copy variant is also closed through
`flFhtPairUpdateStoredAddZeroRight`, the generated scaled-matrix theorem
`flFhtScaledSylvesterScheduleMatrixStoredAddZeroRight_sqrtInvNatScale_error_bound`,
the computed-preconditioner constructor
`ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleStoredAddZeroRight`,
and the exact-law computed-left event wrappers for the stored-add-zero FHT path.
This charges `fl_add(output, 0)` after every rounded pair update; arbitrary
array-layout, aliasing, or in-place overwrite semantics still need separate
certificates if a concrete routine differs from this model.
The one-pair foundation now also has `fl_mul(output, 1)` and
`fl_sub(output, 0)` writeback/copy variants:
`flFhtPairUpdateStoredMulOne_propagated_error_bound` and
`flFhtPairUpdateStoredSubZeroRight_propagated_error_bound` add the same
per-entry copy radius `fp.u * |flFhtPairUpdate fp p q xhat i|` after the
rounded butterfly.  The ordered-schedule lift is closed through
`flFhtPairScheduleStoredMulOne_propagated_error_bound` and
`flFhtPairScheduleStoredSubZeroRight_propagated_error_bound`, recursively
propagating those copy radii across any concrete pair list.  These two
writeback forms are now lifted through the generated Sylvester/Walsh schedule,
rounded `sqrt(1/2^p)` scaling, columnwise computed-matrix packaging,
computed-preconditioner constructors, and exact-law computed-left event
wrappers via
`flFhtScaledSylvesterScheduleMatrixStoredMulOne_sqrtInvNatScale_error_bound`,
`flFhtScaledSylvesterScheduleMatrixStoredSubZeroRight_sqrtInvNatScale_error_bound`,
`ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleStoredMulOne`,
`ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleStoredSubZeroRight`,
and the matching `signedHadamardUniformRowTraceProbability_eventProb_...`
wrappers.  The Rademacher and uniform-row sampling laws are still exact; only
the non-probability FHT writeback arithmetic is charged.
The tighter modified-coordinate writeback variants are now closed through
`flFhtPairUpdateModifiedStoredAddZeroRight`,
`flFhtPairUpdateModifiedStoredMulOne`, and
`flFhtPairUpdateModifiedStoredSubZeroRight`, with generated scaled-matrix
theorems
`flFhtScaledSylvesterScheduleMatrixModifiedStoredAddZeroRight_sqrtInvNatScale_error_bound`,
`flFhtScaledSylvesterScheduleMatrixModifiedStoredMulOne_sqrtInvNatScale_error_bound`,
and
`flFhtScaledSylvesterScheduleMatrixModifiedStoredSubZeroRight_sqrtInvNatScale_error_bound`.
The corresponding computed-preconditioner constructors
`ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleModifiedStoredAddZeroRight`,
`ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleModifiedStoredMulOne`,
and
`ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleModifiedStoredSubZeroRight`
feed the exact-law computed-left event wrappers for exact-sign and stored-sign
variants.  Their propagated budgets add the `fl_add(output,0)`,
`fl_mul(output,1)`, or `fl_sub(output,0)` copy radius only on the two
butterfly outputs written at each pair update and add no copy term on
untouched coordinates.  The same-stage generated-pair order certificates for
these three modified-coordinate routines are now closed by
`flFhtPairUpdateModifiedStoredAddZeroRight_commute_of_disjoint`,
`flFhtPairUpdateModifiedStoredMulOne_commute_of_disjoint`,
`flFhtPairUpdateModifiedStoredSubZeroRight_commute_of_disjoint`, the three
`flFhtPairScheduleModifiedStored..._commute_update_of_forall` list bridges,
and the matching `fhtStagePairs_flFhtPairUpdateModifiedStored..._commute_*`
generated-stage specializations.  The concrete Sylvester-stage order wrappers
`fhtSylvesterStagePairs_disjoint_of_ne`,
`fhtSylvesterStagePairs_pairUpdateExact_commute_of_ne`,
`fhtSylvesterStagePairs_pairUpdateExact_commute_schedule_of_ne`,
`fhtSylvesterStagePairs_flFhtPairUpdate_commute_of_ne`,
`fhtSylvesterStagePairs_flFhtPairUpdate_commute_schedule_of_ne`, and the
matching
`fhtSylvesterStagePairs_flFhtPairUpdateModifiedStored..._commute_*` theorems
specialize the same no-alias/list-order facts to
`fhtSylvesterStagePairs p stage`.  The companion no-touch theorems
`flFhtPairSchedule_apply_of_forall_not_mem`,
`flFhtPairScheduleModifiedStoredAddZeroRight_apply_of_forall_not_mem`,
`flFhtPairScheduleModifiedStoredMulOne_apply_of_forall_not_mem`,
`flFhtPairScheduleModifiedStoredSubZeroRight_apply_of_forall_not_mem`, and
the matching `fhtStagePairs_flFhtPairSchedule..._apply_of_forall_not_mem`
wrappers prove that a coordinate outside every scheduled pair is carried
unchanged by the base rounded and modified-coordinate schedules.  The matching
propagated-budget theorems
`fhtPairSchedulePropagatedErrorBudget_apply_of_forall_not_mem`,
`fhtPairScheduleModifiedStoredAddZeroRightPropagatedErrorBudget_apply_of_forall_not_mem`,
`fhtPairScheduleModifiedStoredMulOnePropagatedErrorBudget_apply_of_forall_not_mem`,
`fhtPairScheduleModifiedStoredSubZeroRightPropagatedErrorBudget_apply_of_forall_not_mem`,
and the matching generated-stage wrappers prove that such an entry keeps
exactly its incoming error radius through the base rounded and
modified-coordinate budget recurrences; this is not asserted for all-coordinate
copy routines, which intentionally rewrite every entry.  The concrete
Sylvester/Walsh wrappers
`flFhtSylvesterSchedule_apply_of_forall_not_mem`,
`flFhtSylvesterScheduleModifiedStoredAddZeroRight_apply_of_forall_not_mem`,
`flFhtSylvesterScheduleModifiedStoredMulOne_apply_of_forall_not_mem`,
`flFhtSylvesterScheduleModifiedStoredSubZeroRight_apply_of_forall_not_mem`,
and the matching `fhtSylvesterSchedule...PropagatedErrorBudget...` theorems
specialize the same value/budget preservation to the full generated schedule
`fhtSylvesterSchedulePairs p`.  The one-stage wrappers
`flFhtSylvesterStageSchedule_apply_of_forall_not_mem`,
`flFhtSylvesterStageScheduleModifiedStoredAddZeroRight_apply_of_forall_not_mem`,
`flFhtSylvesterStageScheduleModifiedStoredMulOne_apply_of_forall_not_mem`,
`flFhtSylvesterStageScheduleModifiedStoredSubZeroRight_apply_of_forall_not_mem`,
and the matching `fhtSylvesterStageSchedule...PropagatedErrorBudget...`
theorems specialize it to `fhtSylvesterStagePairs p stage`.  These wrappers add
no probability-law change and no extra floating-point term; they expose the
same no-touch fact at the concrete generated Sylvester interfaces.
For the uniform row
sketch after preprocessing, `ComputedUniformRowScaleDen` records the computed
`sqrt(s / m)` scaling denominator before the final rounded divisions.
`uniformRowSampleIncrementWithComputedDen_ideal_error_bound` charges the
difference between the computed denominator and the ideal denominator, and
`fl_uniformRowSampleSketch_computedDen_total_error_bound` adds that scalar
denominator term to the rounded-division term.  The exact-denominator
specialization `fl_uniformRowSampleSketch_computedDen_total_error_bound_exact`
reduces to the ordinary rounded division bound.
`ComputedUniformRowScaleDen.flSqrtExactInput` instantiates the certificate for a
single rounded square-root primitive when the input ratio `(s : R) * (m : R)^-1`
is supplied exactly and `fp.u < 1`; rounded formation of that ratio remains a
separate scalar-computation obligation for that exact-input constructor.
`ComputedUniformRowScaleDen.flDivThenSqrt` instantiates the natural fully
computed scalar routine `fl_sqrt (fl_div (s : R) (m : R))`, with denominator
radius
`uniformRowSampleScaleDen s * (Real.sqrt (1 + fp.u) * fp.u + fp.u)`.
`ComputedUniformRowScaleDen.flInvMulThenSqrt` instantiates the alternative
routine `fl_sqrt (fl_mul (s : R) (fl_div 1 (m : R)))`, charging rounded
reciprocal-as-division, rounded multiplication by `s`, and rounded square root
with denominator radius
`uniformRowSampleScaleDen s * (Real.sqrt ((1 + fp.u) * (1 + fp.u)) * fp.u + (2 * fp.u + fp.u ^ 2))`.
`ComputedUniformRowScaleDen.flSqrtDivSqrt` instantiates the split-square-root
routine `fl_div (fl_sqrt (s : R)) (fl_sqrt (m : R))`, charging two rounded
square roots and the rounded scalar division with denominator radius
`uniformRowSampleScaleDen s * ((3 * fp.u + fp.u ^ 2) / (1 - fp.u))`.
`ComputedUniformRowScaleDen.flSqrtMulInvSqrt` instantiates the
square-root-times-reciprocal-square-root routine
`fl_mul (fl_sqrt (s : R)) (fl_div 1 (fl_sqrt (m : R)))`, charging two rounded
square roots, the rounded reciprocal of `sqrt(m)`, and the final rounded
multiplication with denominator radius
`uniformRowSampleScaleDen s * ((4 * fp.u + 3 * fp.u ^ 2 + fp.u ^ 3) / (1 - fp.u))`.
The final actual-input SRHT endpoint selects this routine through
`uniformRowFlSqrtMulInvSqrtScaleDen` and
`signedHadamardUniformRowTraceProbability_eventProb_scaledPatternStoredSignComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess`.
The finite signed-mixing exact-basis and actual-input endpoints now select
the same concrete denominator routine at output dimension `r`, so the exact
denominator is `sqrt(s/r)` and the computed routine is
`fl_mul (fl_sqrt (s : R)) (fl_div 1 (fl_sqrt (r : R)))`:
`signedMixingUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform`,
`signedMixingUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform`, and
`signedMixingUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_total_budget`.
The same concrete denominator routine is now selected by the CountSketch
collision-free orthonormal-basis and actual-input endpoints, and by the
non-injective downstream row-sampling finite-Loewner sample-budget endpoints:
`countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta`,
`countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta`,
`countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget`,
`countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_coeff_budget`,
`countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_coeff_budget`,
`countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_coeff_budget_expanded`,
`countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_frobNorm_budget`,
`countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_frobNorm_budget`, and
`countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_frobNorm_budget_expanded`.
The stored-sign actual-input collision-free endpoint selects the same concrete
denominator routine and additionally charges the sign table by the three
modeled rounded-copy paths:
`countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget`,
`countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignAddZeroRightComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget`, and
`countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignSubZeroRightComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget`.
Exact hash/sign/row laws and the analysis factorization `A=U C` remain exact;
computed non-probability objects are the stored signs, sparse apply,
denominator, row divisions, and sampled-Gram dot products.
The permuted-bucket stored-sign actual-input endpoint additionally closes exact
supplied per-bucket traversal orders:
`countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignPermutedComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget`,
`countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignAddZeroRightPermutedComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget`, and
`countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignSubZeroRightPermutedComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget`.
The bucket orders are exact discrete implementation choices; sign storage,
sparse signed products, accumulation in the selected order, denominator
formation, row divisions, and sampled-Gram dot products are computed and
charged.  The probability loss remains `m^2/r + deltaSample`, with no
`deltaComp`, perturbation-event hypothesis, or certificate-existence
assumption.
The tree-reduced stored-sign actual-input collision-free endpoint additionally
charges exact supplied per-bucket tree reductions through the tree-depth
roundoff factors:
`countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignTreeComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget`,
`countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignAddZeroRightTreeComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget`, and
`countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignSubZeroRightTreeComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget`.
The tree shapes are exact discrete implementation choices; arithmetic along
the tree, denominator formation, row divisions, and Gram dot products are
computed and charged.
The exact-coefficient wrappers keep the irreducible CountSketch loss
`2 * r^{-1} * sum_{j,k,a != b} (A_aj * A_bk)^2 / etaCS^2` instead of
immediately replacing it by `2 * ||A||_F^4 / (r * etaCS^2)`.
The expanded equal-radius wrappers replace `etaCS = etaRow = eps / 2`
inside the Lean theorem surface, giving the exact-coefficient condition
`8 * r^{-1} * sum_{j,k,a != b} (A_aj * A_bk)^2 / eps^2
 + 4 * r * m^2 * ||A||_F^4 / (s * eps^2) <= delta` and the readable
condition `8 * ||A||_F^4 / (r * eps^2)
 + 4 * r * m^2 * ||A||_F^4 / (s * eps^2) <= delta`.
The downstream finite-cover CountSketch wrappers
`countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob_add_row`,
`countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_cover_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget`, and
`countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_cover_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget`
replace the CountSketch Frobenius preprocessing radius by the finite-cover
Loewner radius `eta + L * (2*rho + rho^2)`, then add `etaRow` and the same
realized FP budget.  Their exact target loss is
`sum_alpha 2*r^{-1}*sum_{a != b} ((A*z_alpha)_a*(A*z_alpha)_b)^2/eta^2
 + 2*r^{-1}*sum_{j,k,a != b} (A_aj*A_bk)^2/L^2
 + r*m^2*||A||_F^4/(s*etaRow^2)`.
The downstream finite-cover wrappers now also have product-grid
specializations
`countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_coeff_add_frob_add_row`,
`countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget`, and
`countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget`.
They instantiate the finite cover by the exact grid vectors
`z_a(j) = grid (a j)` for `a : Fin n -> alpha`, under
`sqrt(n)*deltaGrid <= rho`, and keep the exact coefficient loss
`sum_{a : Fin n -> alpha} 2*r^{-1}*sum_{p != q}
((A*z_a)_p*(A*z_a)_q)^2/eta^2
 + 2*r^{-1}*sum_{j,k,p != q} (A_pj*A_qk)^2/L^2
 + r*m^2*||A||_F^4/(s*etaRow^2)`.
The final concrete-denominator wrapper selects
`fl_mul (fl_sqrt (s : R)) (fl_div 1 (fl_sqrt (r : R)))`.  Thus the exact
product grid, exact hash/sign laws, and exact row-sampling law remain analysis
objects, while sparse apply, denominator formation, sampled-row divisions, and
sampled-Gram dot products are all charged by the realized FP budget.
The product-grid sparse-Gram branch now also has an orthonormal-basis
specialization:
`countSketchProbability_eventProb_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_gridNorm_add_nat_orthonormal`,
`countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_gridNorm_add_nat_orthonormal`,
and the stored-sign concrete wrappers
`countSketchProbability_eventProb_flSparseGramDotWithFlStoredSign_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_orthonormal_budget`,
`countSketchProbability_eventProb_flSparseGramDotWithFlStoredSignAddZeroRight_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_orthonormal_budget`, and
`countSketchProbability_eventProb_flSparseGramDotWithFlStoredSignSubZeroRight_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_orthonormal_budget`.
For exact `U` with `U^T U = I`, the product-grid loss reduces to
`sum_a 2*||z_a||_2^4/(r*eta^2) + 2*n^2/(r*L^2)`, with order
`Theta((sum_a ||z_a||_2^4/eta^2 + n^2/L^2)/r)`.
The stored-sign version charges the stored sign table, sparse signed products,
bucket accumulation, and rounded Gram dot products; the grid and probability
laws remain exact.
The same orthonormal simplification is now composed through downstream uniform
row sampling for the ordinary stored-sign path:
`countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget`,
`countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget`,
and the concrete sign-copy wrappers
`countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget`,
`countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignAddZeroRightComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget`, and
`countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignSubZeroRightComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget`.
The final downstream loss is
`sum_a 2*||z_a||_2^4/(r*eta^2) + 2*n^2/(r*L^2) +
r*(m*n)^2/(s*etaRow^2)`, with order
`Theta((sum_a ||z_a||_2^4/eta^2 + n^2/L^2)/r +
r*m^2*n^2/(s*etaRow^2))`.  It charges stored signs, sparse products, bucket
accumulation, concrete denominator formation, sampled-row divisions, and
sampled-Gram dot products.
The orthonormal downstream simplification is also closed for fixed per-bucket
orders and exact supplied bucket trees via
`countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget`,
`countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignAddZeroRightPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget`,
`countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignSubZeroRightPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget`,
`countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget`,
`countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignAddZeroRightTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget`, and
`countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignSubZeroRightTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget`.
The sufficient exact loss and order are unchanged from the ordinary
orthonormal downstream formula.  The only difference is the charged computed
radius: fixed-order bucket accumulation uses the selected exact order, while
tree-reduced accumulation uses exact tree shapes and the tree-depth
`gammaValid` hypotheses.
The non-injective CountSketch exact-law foundation also now includes fixed
test-vector quadratic-form bounds:
`countSketchProbability_expectationReal_rowGram_quadratic_error_sq_le`,
`countSketchProbability_expectationReal_rowGram_quadratic_error_sq_le_vecNorm`,
`countSketchProbability_expectationReal_rowGram_quadratic_error_sq_le_frobNorm`,
and
`countSketchProbability_eventProb_abs_rowGram_quadratic_error_le_ge_one_sub_delta_of_coeff_budget`.
For exact \(A\) and fixed exact \(x\), the irreducible failure term is
`2 * r^{-1} * sum_{a != b} ((A*x)_a * (A*x)_b)^2 / eta^2`, with readable
orders `O(||A*x||_2^4 / (r * eta^2))` and
`O(||A||_F^4 * ||x||_2^4 / (r * eta^2))`. This is exact-probability
infrastructure for later finite-cover/subspace-embedding work, not a
floating-point endpoint.
The finite-test wrapper
`countSketchProbability_eventProb_forall_abs_rowGram_quadratic_error_le_ge_one_sub_delta_of_sum_coeff_budget`
unions the same tail over any finite exact test set. Its irreducible loss is
`sum_alpha 2 * r^{-1} * sum_{a != b} ((A*x_alpha)_a * (A*x_alpha)_b)^2 / eta_alpha^2`,
with readable upper forms using `||A*x_alpha||_2^4` or
`||A||_F^4 * ||x_alpha||_2^4`. The deterministic cover upgrade is now proved by
`countSketchProbability_eventProb_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob`
and
`countSketchProbability_eventProb_rowGram_twoSidedLoewner_cover_ge_one_sub_delta_of_sum_coeff_add_frob_budget`.
For a finite unit-ball cover of radius `rho`, common test threshold `eta`, and
Frobenius coarse threshold `L`, the two-sided Loewner radius is
`eta + L * (2 * rho + rho^2)`, and the irreducible loss is the finite-test
loss plus
`2 * r^{-1} * sum_{j,l,a != b} (A_aj * A_bl)^2 / L^2`. The readable order is
`O(sum_alpha ||A*x_alpha||_2^4 / (r * eta^2) + ||A||_F^4 / (r * L^2))`.
The exact readable theorem surface is also Lean-proved by
`countSketchProbability_eventProb_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_vecNorm_add_frobNorm`
and
`countSketchProbability_eventProb_rowGram_twoSidedLoewner_cover_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget`.
This is still exact-law infrastructure, not a floating-point endpoint.
The supplied finite-cover hypothesis now has a constructive product-grid
specialization.  If an exact one-dimensional grid `grid : alpha -> R` covers
`[-1,1]` with radius `deltaGrid`, `0 <= deltaGrid`, and
`sqrt(n) * deltaGrid <= rho`, then
`finiteUnitBallCover_product_grid` proves that the coordinatewise product grid
`z_a(j) = grid (a j)`, indexed by `a : Fin n -> alpha`, is an exact
unit-ball cover of radius `rho`; its cardinality is `|alpha|^n` by
`fintype_card_product_grid_index`.  The exact CountSketch product-grid
wrappers
`countSketchProbability_eventProb_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_vecNorm_add_frobNorm`
and
`countSketchProbability_eventProb_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget`
therefore replace the abstract finite cover by the explicit loss
`sum_{a : Fin n -> alpha} 2*||A*z_a||_2^4/(r*eta^2)
 + 2*||A||_F^4/(r*L^2)`.
In the regime of fixed exact `A`, grid, `eta`, and `L`, this loss is
`Theta((sum_a ||A*z_a||_2^4/eta^2 + ||A||_F^4/L^2)/r)` when the numerator is
nonzero, and it tends to zero as `r -> infinity`.  The product grid and its
cardinality are exact analysis objects, not quantities computed by Algorithm 3.
The computed finite-cover transfer is now proved by
`countSketchRowGramTwoSidedLoewnerCoverEvent_subset_flSparseGramDotRowGramTwoSidedLoewnerEvent`,
`countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob`,
and
`countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_cover_ge_one_sub_delta_of_sum_coeff_add_frob_budget`.
It preserves the same exact finite-test-plus-Frobenius probability loss, but
the event is now the computed sparse Gram Loewner event with radius
`eta + L * (2 * rho + rho^2) + T_CSGram_fp(h, omega, A)`.  Thus exact
hash/sign probabilities and the finite cover remain analysis objects, while
rounded sparse signed products, bucket accumulation, and Gram dot products are
charged by `countSketchSparseGramFullFpPerturbBudget`.  The irreducible and
readable probability orders are unchanged from the exact-cover theorem; the
new term is deterministic floating-point radius, not a probability loss.
The readable loss is also Lean-proved by
`countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_vecNorm_add_frobNorm`
and its direct target-budget wrapper
`countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_cover_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget`,
which use
`sum_alpha 2 * ||A*x_alpha||_2^4 / (r * eta^2) + 2 * ||A||_F^4 / (r * L^2)`.
The computed product-grid versions
`countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_vecNorm_add_frobNorm`
and
`countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget`
combine the same exact product grid with the computed sparse Gram event.  The
probability loss remains
`sum_{a : Fin n -> alpha} 2*||A*z_a||_2^4/(r*eta^2)
 + 2*||A||_F^4/(r*L^2)`, while the event radius is
`eta + L*(2*rho + rho^2) + T_CSGram_fp(h, omega, A)`.  Rounded sparse signed
products, bucket accumulation, and rounded Gram dot products are charged by
the concrete sparse-Gram budget; the exact grid and exact hash/sign laws do
not introduce floating-point probability or cover-construction terms.
The lower-level CountSketch sign-storage arithmetic is now also proved as a
deterministic implementation substrate.  If the realized Rademacher sign table
is first copied by `fl_mul sign_i 1`, `fl_add sign_i 0`, or `fl_sub sign_i 0`,
then `preconditionRows_countSketchRows_storedSign_entry_error_bound`,
`fl_countSketchSparseApplyEntry_withStoredSign_error_bound`,
`fl_countSketchSparseApplyWithStoredSign_entry_error_bound`, and
`fl_countSketchSparseGramDotWithStoredSign_perturb_bound` add the explicit
bucket term `sum_{k:h(k)=i} signhat.abs_error_k * |A_kj|` to the sparse-apply
radius before the rounded Gram-dot budget is formed.  The concrete endpoints
`fl_countSketchSparseGramDotWithFlStoredSign_perturb_bound`,
`fl_countSketchSparseGramDotWithFlStoredSignAddZeroRight_perturb_bound`, and
`fl_countSketchSparseGramDotWithFlStoredSignSubZeroRight_perturb_bound` use
the already proved absolute-one sign storage radius `u`.  These are
deterministic Gram perturbation theorems.
The product-grid probability wrapper using the stored-sign event is now also
closed.  The generic event
`countSketchFlSparseGramDotWithStoredSignRowGramTwoSidedLoewnerEvent` and
subset theorem
`countSketchRowGramTwoSidedLoewnerCoverEvent_subset_flSparseGramDotWithStoredSignRowGramTwoSidedLoewnerEvent`
transfer the exact product-grid CountSketch event to a computed sparse-Gram
event whose radius is
`eta + L*(2*rho + rho^2) + T_CSGram_stored(h, omega, A)`.  The readable and
target-budget wrappers
`countSketchProbability_eventProb_flSparseGramDotWithStoredSign_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_vecNorm_add_frobNorm`
and
`countSketchProbability_eventProb_flSparseGramDotWithStoredSign_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget`
preserve the same exact-law product-grid loss
`sum_{a : Fin n -> alpha} 2*||A*z_a||_2^4/(r*eta^2)
 + 2*||A||_F^4/(r*L^2)`.
The three concrete sign-copy endpoints
`countSketchProbability_eventProb_flSparseGramDotWithFlStoredSign_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget`,
`countSketchProbability_eventProb_flSparseGramDotWithFlStoredSignAddZeroRight_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget`,
and
`countSketchProbability_eventProb_flSparseGramDotWithFlStoredSignSubZeroRight_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget`
instantiate `fl_mul sign_i 1`, `fl_add sign_i 0`, and `fl_sub sign_i 0`.
The probability-loss order remains
`Theta((sum_a ||A*z_a||_2^4/eta^2 + ||A||_F^4/L^2)/r)` for fixed exact
input/grid/threshold data with nonzero numerator; sign storage contributes
only the deterministic floating-point radius.
The same product-grid stored-sign endpoint is now also closed for any fixed
per-bucket memory order.  `Preconditioning.lean` exposes the permuted sparse
apply and Gram budgets
`fl_countSketchSparseApplyWithStoredSignPermuted_entry_error_bound` and
`fl_countSketchSparseGramDotWithStoredSignPermuted_perturb_bound`, plus the
product-grid wrappers
`countSketchProbability_eventProb_flSparseGramDotWithStoredSignPermuted_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_vecNorm_add_frobNorm`
and
`countSketchProbability_eventProb_flSparseGramDotWithStoredSignPermuted_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget`.
The concrete sign-copy variants
`countSketchProbability_eventProb_flSparseGramDotWithFlStoredSignPermuted_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget`,
`countSketchProbability_eventProb_flSparseGramDotWithFlStoredSignAddZeroRightPermuted_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget`,
and
`countSketchProbability_eventProb_flSparseGramDotWithFlStoredSignSubZeroRightPermuted_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget`
instantiate the same three stored-sign copy modes.  The bucket order itself is
an exact discrete index choice depending on the realized hash, not a
floating-point real computation.  The event radius is
`eta + L*(2*rho + rho^2) + T_CSGram_stored_permuted(h, omega, order, A)`;
the exact product-grid probability loss and its
`Theta((sum_a ||A*z_a||_2^4/eta^2 + ||A||_F^4/L^2)/r)` order are unchanged.
This closes fixed left-to-right bucket folds in any chosen per-bucket order;
parallel reassociation, aliasing, and other non-permutation memory layouts
remain separate implementation routines.
The sparse-Gram stored-sign product-grid endpoint is now also closed for an
explicit binary summation tree in each bucket.  `Preconditioning.lean` exposes
`fl_countSketchSparseApplyEntryTree_error_bound`,
`fl_countSketchSparseApplyTree_entry_error_bound`,
`fl_countSketchSparseGramDotTree_perturb_bound`,
`fl_countSketchSparseApplyWithStoredSignTree_entry_error_bound`,
`fl_countSketchSparseGramDotWithStoredSignTree_perturb_bound`,
and the product-grid wrappers
`countSketchProbability_eventProb_flSparseGramDotWithStoredSignTree_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_vecNorm_add_frobNorm`
and
`countSketchProbability_eventProb_flSparseGramDotWithStoredSignTree_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget`,
with concrete `Tree` sign-copy variants for `fl_mul sign_i 1`,
`fl_add sign_i 0`, and `fl_sub sign_i 0`.  The tree shapes are exact
discrete algorithm choices; the computed radius charges stored signs, rounded
sparse products, tree-depth bucket accumulation, and rounded length-`r` Gram
dot products:
`eta + L*(2*rho + rho^2) + T_CSGram_stored_tree(h, omega, tree, A)`.
For fixed realized data,
`E_CS_tree = Theta((u + gamma_depth_i) * bucket_column_one_norm)`, and balanced
bucket trees give the interpretable order
`Theta(u*(1 + log(bucket_size_i + 1))*bucket_column_one_norm)`.  The exact
product-grid probability loss remains
`Theta((sum_a ||A*z_a||_2^4/eta^2 + ||A||_F^4/L^2)/r)`.  This closes the
tree-reduced sparse-Gram path; the downstream uniform-row tree-reduced
composition is closed below.  Parallel/aliasing sparse-sketch layouts,
lower-level hash/sign generation, and optimal CountSketch concentration remain
separate targets.
The stored-sign sparse-apply basis is now also threaded through the downstream
uniform-row product-grid route.  `UniformRowSamplingFP.lean` exposes the
probability-one stored-sign perturbation theorem
`countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one`,
the product-grid wrappers
`countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_coeff_add_frob_add_row`
and
`countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget`,
and the concrete denominator/sign-copy endpoints for `fl_mul sign_i 1`,
     `fl_add sign_i 0`, and `fl_sub sign_i 0`.  The exact product-grid plus row
loss is unchanged from the exact-sign downstream theorem; the event radius is
`eta + L*(2*rho + rho^2) + etaRow + T_CS_row_stored(h, omega, sigma, A)`,
where the deterministic term expands into stored-sign sparse-apply error,
computed denominator error, rounded row divisions, and rounded sampled-Gram
dot products.
The same downstream route is now also closed for fixed exact per-bucket
permutations.  `UniformRowSamplingFP.lean` exposes
`countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted`,
`countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget`,
`countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one`,
and the product-grid endpoint
`countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget`,
with add-zero and subtract-zero sign-copy siblings.  The bucket order is exact
discrete data depending on the realized hash; the computed radius additionally
charges accumulation in that selected order, while the exact product-grid plus
row-sampling probability loss is unchanged.  This closes fixed per-bucket
permutation layouts for the stored-sign downstream path.  Parallel
reassociation and aliasing sparse-sketch implementations remain separate
paths.
The same downstream route is now also closed for exact binary bucket trees.
`UniformRowSamplingFP.lean` exposes
`countSketchSparseComputedPreconditionedBasisWithStoredSignTree`,
`countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget`,
`countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one`,
and the product-grid endpoint
`countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget`,
with add-zero and subtract-zero sign-copy siblings.  The tree shape and
trailing zero leaf are exact discrete data depending on the realized hash; the
computed radius additionally charges tree-depth bucket accumulation.  The
event radius is
`eta + L*(2*rho + rho^2) + etaRow + T_CS_row_stored_tree(h, omega, sigma, A)`,
the exact product-grid plus row-sampling probability loss is unchanged, and
balanced bucket trees give the readable sampled-basis order
`Theta(u*(1 + log(bucket_size_i + 1))*bucket_column_one_norm/sqrt(s/r))`.
This closes the tree-reduced stored-sign downstream path without adding any
perturbation-event or certificate-existence assumption.
The stored-sign downstream product-grid route now also has final concrete
denominator wrappers for `fl_sqrt` with exact input ratio, `fl_sqrt(fl_div s r)`,
`fl_sqrt(fl_mul s (fl_div 1 r))`, and
`fl_div (fl_sqrt s) (fl_sqrt r)`, namely
`countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtExactInputDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget`,
`countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlDivThenSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget`,
`countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlInvMulThenSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget`, and
`countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtDivSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget`.
Their probability loss is unchanged; only the deterministic denominator
factor changes to `u`, `sqrt(1+u)*u + u`,
`sqrt((1+u)*(1+u))*u + 2*u + u^2`, or `(3*u + u^2)/(1-u)`.
The exact-input square-root route assumes the scalar ratio `s/r` has already
been supplied exactly; if that ratio is computed in floating point, use one of
the fully computed divide/multiply routes instead.  The older generic
`WithComputedDen` theorem remains infrastructure for any future denominator
routine not represented by these concrete certificates.
These computed surfaces do not change
the ideal Rademacher/uniform probability laws; they make the extra arithmetic
explicit when a concrete transform-generation or denominator routine is
supplied.
For the SRHT/uniform-row corollaries, the row-sampling probabilities are the
uniform law `1 / m`; the computed quantity is the implemented preprocessed
basis `Vhat`.  The correction layer
`signedHadamardComputedPreconditionedFlUniformRowPerturbEvent` and the theorems
`signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta`,
`signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_constBudget`,
and
`signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_constBudget_srht_log_preprocess`
add a separate `delta_comp` failure budget and perturbation radius for forming
`Vhat`, including Hadamard/sign arithmetic, computed or stored basis vectors,
computed scale denominators, row scaling, and Gram dot products.  The
two-sided preprocessing surface now also has
`fl_preconditionElementsWithComputed_total_error_bound`, which measures
`fl(PiLhat A PiRhat)` against the ideal `PiL A PiR` and charges both computed
projection matrices.
When those projection matrices are formed from computed bases or
singular-vector tables, `basisColumnProjector` represents the ideal projector
`Q Q^T`, `ComputedPreconditioner.flBasisColumnProjector` packages the computed
projector `fl(Qhat Qhat^T)`, and
`fl_basisColumnProjector_total_error_bound` charges projector-formation
roundoff plus both occurrences of the computed basis error.  The two-sided
wrapper `fl_preconditionElementsWithComputedBasisProjectors_total_error_bound`
then plugs those computed projectors directly into the existing
`fl(PiLhat A PiRhat)` surface, with the sampling laws still treated as exact.
For upstream QR/SVD or singular-vector routines, the named constructor
`ComputedMatrix.ofEntrywiseBound` and the projector handoff
`ComputedPreconditioner.flBasisColumnProjectorOfCertifiedBasis` expose the
routine output `Qhat` and its entrywise radius `E` directly.  The theorem
`fl_basisColumnProjector_of_certifiedBasis_entry_error_bound` proves
`|fl(Qhat Qhat^T)_ij - (Q Q^T)_ij|` is bounded by
`gamma_k * sum |Qhat_i a| |Qhat_j a| + sum E_i a |Qhat_j a| +
sum |Q_i a| E_j a`, and
`fl_preconditionElementsWithCertifiedBasisProjectors_total_error_bound` plugs
left and right certified projectors into the two-sided Algorithm 3
preprocessing theorem.  The concrete QR/SVD generation proof remains a
separate obligation; this bridge prevents the implementation-facing theorem
from silently using exact singular vectors or exact projectors.
For QR/SVD routines whose basis is determined only up to signs or a right
orthogonal rotation, `basisColumnProjector_matMulRectRight_orthogonal` proves
`(Q O)(Q O)^T = Q Q^T` when `O` is orthogonal.  The generic theorem
`fl_basisColumnProjector_entry_error_budget_bound_rightOrthogonalReference`
therefore accepts a `ComputedMatrix` certificate against the rotated exact
reference `Q O` while bounding the projector against the analysis object
`Q Q^T`.  The named entrywise handoffs
`fl_basisColumnProjector_of_rightOrthogonalCertifiedBasis_entry_error_bound`
and
`fl_basisColumnProjector_of_rightOrthogonalCertifiedStoredBasis_entry_error_bound`
expose the same correction for direct and generated-then-stored QR/SVD basis
tables.  This charges the computed basis and storage errors, while the
sign/rotation ambiguity itself is an exact analysis equivalence; sampling
probabilities and sampling laws remain exact.
If the routine output is not the final table used by the algorithm, the
generation-plus-storage handoff
`ComputedMatrix.ofEntrywiseBoundThenStorage` keeps the two stages separate:
`Qraw` is certified against the exact analysis basis `Q` by an entrywise radius
`E`, while the stored table `Qstore` is certified against `Qraw` by a storage
radius `C`.  The projector budget
`certifiedStoredBasisProjectorEntryErrorBudget` then uses the actual stored
table and the combined radius `C + E`:
`gamma_k * sum |Qstore_i a| |Qstore_j a| + sum (C_i a + E_i a) *
|Qstore_j a| + sum |Q_i a| * (C_j a + E_j a)`.
The concrete constructors `ComputedMatrix.ofEntrywiseBoundStoredMulOne`,
`ComputedMatrix.ofEntrywiseBoundStoredAddZeroRight`, and
`ComputedMatrix.ofEntrywiseBoundStoredSubZeroRight` instantiate
`C_ij = fp.u * |Qraw_ij|` for rounded copy paths
`fl_mul Qraw_ij 1`, `fl_add Qraw_ij 0`, and `fl_sub Qraw_ij 0`.
`ComputedPreconditioner.flBasisColumnProjectorOfCertifiedStoredBasis` and
`fl_preconditionElementsWithCertifiedStoredBasisProjectors_total_error_bound`
then feed the stored projectors into the same two-sided Algorithm 3
preprocessing surface.  This still leaves the actual QR/SVD/singular-vector
generation proof as a separate obligation, but it no longer conflates routine
error with table-storage error.
The same generated-then-stored handoff is now available when the raw
QR/SVD/basis routine proves a Frobenius, per-column Euclidean, or rectangular
operator-norm certificate instead of an entrywise one.  The constructors
`ComputedMatrix.ofFrobeniusBoundThenStorage`,
`ComputedMatrix.ofColumnVecNorm2BoundThenStorage`, and
`ComputedMatrix.ofRectOpNorm2BoundThenStorage` convert the raw normwise
certificate to the entry radius `eta`, `eta_a`, or `eta`, add the storage
radius `C`, and feed the stored projector constructors
`ComputedPreconditioner.flBasisColumnProjectorOfFrobeniusCertifiedStoredBasis`,
`ComputedPreconditioner.flBasisColumnProjectorOfColumnwiseCertifiedStoredBasis`,
and `ComputedPreconditioner.flBasisColumnProjectorOfOpNormCertifiedStoredBasis`.
The corresponding two-sided Algorithm 3 wrappers
`fl_preconditionElementsWithFrobeniusCertifiedStoredBasisProjectors_total_error_bound`,
`fl_preconditionElementsWithColumnwiseCertifiedStoredBasisProjectors_total_error_bound`,
and `fl_preconditionElementsWithOpNormCertifiedStoredBasisProjectors_total_error_bound`
plug those stored projectors into `fl(PiLhat A PiRhat)`.  Sampling
probabilities and laws remain exact mathematical inputs throughout.
If the storage routine proves only a normwise storage bound rather than an
entrywise `C`, the constructors
`ComputedMatrix.ofEntrywiseBoundThenFrobeniusStorage`,
`ComputedMatrix.ofFrobeniusBoundThenFrobeniusStorage`,
`ComputedMatrix.ofColumnVecNorm2BoundThenColumnVecNorm2Storage`, and
`ComputedMatrix.ofRectOpNorm2BoundThenRectOpNorm2Storage` convert the storage
certificate to the appropriate entry radius before projector formation.  The
named projector theorems
`fl_basisColumnProjector_of_frobeniusCertifiedFrobeniusStoredBasis_entry_error_bound`,
`fl_basisColumnProjector_of_columnwiseCertifiedColumnwiseStoredBasis_entry_error_bound`,
and `fl_basisColumnProjector_of_opNormCertifiedOpNormStoredBasis_entry_error_bound`
then charge raw generation, normwise storage, and rounded projector dot
products.  Two-sided preprocessing uses the existing computed-basis projector
surface once these constructors build the `ComputedMatrix` certificates.
If the raw routine certificate is Frobenius, columnwise, or rectangular
operator-norm rather than entrywise, the stored-table constructors
`ComputedMatrix.ofFrobeniusBoundThenStorage`,
`ComputedMatrix.ofColumnVecNorm2BoundThenStorage`, and
`ComputedMatrix.ofRectOpNorm2BoundThenStorage` convert the raw certificate to
an entrywise radius and then add the actual storage radius `C`.  The projector
theorems
`fl_basisColumnProjector_of_frobeniusCertifiedStoredBasis_entry_error_bound`,
`fl_basisColumnProjector_of_columnwiseCertifiedStoredBasis_entry_error_bound`,
and `fl_basisColumnProjector_of_opNormCertifiedStoredBasis_entry_error_bound`
therefore bound `fl(Qstore Qstore^T) - Q Q^T` with radii `C_ia + eta`,
`C_ia + eta_a`, or `C_ia + eta`, respectively.  Concrete rounded-copy storage
can instantiate `C` with the existing `flMulOne`, `flAddZeroRight`, or
`flSubZeroRight` entry-error theorems.  Sampling probabilities and laws remain
exact.
For QR/SVD/basis routines whose available certificate is normwise rather than
entrywise, `ComputedMatrix.ofFrobeniusBound` converts
`||Qhat - Q||_F <= eta` into a uniform entrywise radius.  The corresponding
projector handoff
`ComputedPreconditioner.flBasisColumnProjectorOfFrobeniusCertifiedBasis` proves
`|fl(Qhat Qhat^T)_ij - (Q Q^T)_ij|` is bounded by
`gamma_k * sum |Qhat_i a| |Qhat_j a| + sum eta * |Qhat_j a| +
sum |Q_i a| * eta`, and
`fl_preconditionElementsWithFrobeniusCertifiedBasisProjectors_total_error_bound`
plugs left and right Frobenius-certified projectors into the same two-sided
preprocessing surface.  This is still a certificate-transfer theorem: a
concrete QR/SVD routine must separately prove the displayed Frobenius radius.
For routines that certify each computed basis vector separately,
`ComputedMatrix.ofColumnVecNorm2Bound` converts
`||Qhat(:,a) - Q(:,a)||_2 <= eta_a` into the entrywise radius used by the
projector theorem.  The corresponding
`ComputedPreconditioner.flBasisColumnProjectorOfColumnwiseCertifiedBasis`
handoff proves the budget
`gamma_k * sum |Qhat_i a| |Qhat_j a| + sum eta_a * |Qhat_j a| +
sum |Q_i a| * eta_a`, and
`fl_preconditionElementsWithColumnwiseCertifiedBasisProjectors_total_error_bound`
plugs left and right columnwise-certified projectors into `fl(PiLhat A PiRhat)`.
Sampling probabilities and sampling laws are still exact mathematical inputs;
the new terms charge only the computed basis vectors, projector formation, and
rounded preprocessing products.
For routines whose certificate is an operator-2/spectral vector-action bound,
`ComputedMatrix.ofRectOpNorm2Bound` tests the local `rectOpNorm2Le` certificate
on standard basis vectors to obtain the same uniform entrywise radius.
`ComputedPreconditioner.flBasisColumnProjectorOfOpNormCertifiedBasis` and
`fl_preconditionElementsWithOpNormCertifiedBasisProjectors_total_error_bound`
then give the analogous projector and two-sided preprocessing bounds with
radius
`gamma_k * sum |Qhat_i a| |Qhat_j a| + sum eta * |Qhat_j a| +
sum |Q_i a| * eta`.  This is the spectral-certificate transfer surface for
future Davis-Kahan/SVD-style basis routines, not a proof of such a routine.
The concrete table-storage paths `ComputedMatrix.flMulOne`,
`ComputedMatrix.flAddZeroRight`, and `ComputedMatrix.flSubZeroRight` cover a
basis/singular-vector table realized as `fl_mul Q_ij 1`, `fl_add Q_ij 0`, or
`fl_sub Q_ij 0` before projector formation.  The corresponding projector
certificates
`ComputedPreconditioner.flBasisColumnProjectorStoredBasisMulOne`,
`ComputedPreconditioner.flBasisColumnProjectorStoredBasisAddZeroRight`, and
`ComputedPreconditioner.flBasisColumnProjectorStoredBasisSubZeroRight` have
entry radius `fp.u * |Q_ij|` for storage plus the rounded
`fl(Qhat Qhat^T)` dot-product budget.  This closes the three modeled
storage/copy routines; the upstream QR/SVD or singular-vector generation
routine remains a separate `ComputedMatrix` obligation.
The concrete computed-left SRHT-style path is now partially instantiated:
`signedHadamardComputedLeftPreconditionedBasis` models
`Vhat(omega) = fl(Pihat(omega) * U)`, and
`signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one`
proves that the generic computed-`Vhat` perturbation event holds with
probability one under the exact Rademacher/uniform-row law once the supplied
`Pihat(omega)` carries a `ComputedPreconditioner` certificate.  The visible
budget combines the entrywise `Vhat - H D_omega U` budget,
`uniformRowSampleGram_frob_error_bound_of_basis_entrywise_abs`, with the
rounded row-scaling and Gram-dot-product budget after `Vhat` is formed.
`ComputedMatrix` records the analogous entrywise error certificate for a basis
or singular-vector table computed before preprocessing, and
`signedHadamardUniformRowTraceProbability_eventProb_computedLeftInputPreconditioned_fl_uniformRowPerturbEvent_eq_one`
proves the same probability-one perturbation event for
`Vhat(omega) = fl(Pihat(omega) * Uhat)`.  Its named budget
`flPreconditionRowsWithComputedLeftInputEntryErrorBudget` charges rounded
matrix multiplication, transform-entry error, and computed-basis entry error.
`ComputedPreconditioner.exact` and
`signedHadamardExactStoredPreconditioner` instantiate the zero-storage-error
baseline where the realized `H D_omega` matrix is available exactly; the budget
then reduces to rounded formation of `Vhat`, row scaling, and Gram dot
products.  `signedHadamardExactFactorPreconditioner` instead assumes exact
Hadamard/sign factors and charges the rounded formation of `H D_omega` before
the same computed-left `Vhat` event.  The generated Sylvester/Walsh fast-FHT
path now has a functional `ComputedPreconditioner` instantiation through
`signedHadamardSylvesterFhtSchedulePreconditioner`, plus the concrete
add-zero writeback/copy instantiation through
`signedHadamardSylvesterFhtScheduleStoredAddZeroRightPreconditioner`, the
all-coordinate multiply-one/subtract-zero instantiations through
`signedHadamardSylvesterFhtScheduleStoredMulOnePreconditioner` and
`signedHadamardSylvesterFhtScheduleStoredSubZeroRightPreconditioner`, and the
modified-coordinate add/multiply/subtract writeback instantiations through
`signedHadamardSylvesterFhtScheduleModifiedStoredAddZeroRightPreconditioner`,
`signedHadamardSylvesterFhtScheduleModifiedStoredMulOnePreconditioner`, and
`signedHadamardSylvesterFhtScheduleModifiedStoredSubZeroRightPreconditioner`;
remaining generator work is array memory-order/aliasing/overwrite
certification for routines that differ from the modeled all-coordinate or
modified-coordinate writeback paths, random-bit storage formats beyond the
modeled sign-copy paths, and concrete SVD/QR/basis construction routines.
The repository now also defines the uniform finite
Rademacher sign-vector law, proves the first/second moment identities for those
finite signs, proves that signed orthogonal preprocessing holds with probability
one, proves the exact exponential-moment factorization for a signed linear
form, proves scalar Rademacher Hoeffding MGF and two-sided tail bounds, and
proves that a flat Hadamard-style preconditioner gives expected preconditioned
row norm squared `n / m`. It also proves the expected Euclidean row-norm bound
used in Tropp's Lemma 3.3 prelude, by composing that second-moment identity
  with the repository's finite Cauchy-Schwarz/Jensen lemma, and it packages the
  deterministic signed-Hadamard row-norm convexity and `1 / sqrt(m)` Lipschitz
  inputs required by Tropp's Ledoux/Talagrand concentration step. It also
  formalizes the deterministic affine scaling constants that convert Ledoux's
  \([0,1]^m\) upper-tail statement into Tropp's Rademacher-sign statement:
  `unitCubeToRademacherVec` and
  `finiteVecLipschitzWith_scaled_unitCubeToRademacher` record the factor of
  two that changes `exp(-t^2/2)` into `exp(-t^2/8)`. From that expectation
theorem and the local finite-probability Markov and union-bound lemmas, it also
proves a weak all-row
high-probability bound: if the chosen threshold `T` has Markov/union failure
budget at most `delta`, then all signed-Hadamard row norms are at most `T` with
probability at least `1 - delta`. It also proves a coordinate-Hoeffding
all-entry theorem and the induced all-row bound
`rowNormSq <= n * B^2`, then converts that event into the equation (6)
leverage-probability event `leverageScoreProb <= B^2` with a delta-budget
wrapper. It also proves the deterministic uniform-row-sampling rank-one
foundations: `m u_i u_i^T` is PSD, has expectation `I` for an
orthonormal-column basis under uniform row sampling, and is bounded by
`m n B^2 I` whenever `leverageScoreProb <= B^2`; the signed-Hadamard
high-probability event is composed with that Loewner boundedness result. The
library now also proves the downstream iid uniform sample-average concentration
route in tail-budget form: the uniform sample Gram matrix satisfies a two-sided
finite-Loewner error event with probability at least `1 - δ` whenever the
displayed trace-exponential tails are budgeted by `δ`. It also composes the
signed-Hadamard preprocessing event and the iid uniform row-sampling event on
the product probability space, giving the two-sided uniform sample-Gram event
with probability at least `1 - (δPre + δSample)` for the scoped
coordinate-Hoeffding route. The fully floating-point uniform sketch is also
proved on the same joint probability space: rounded row scaling and rounded
dot products enlarge the two-sided finite-Loewner radius by the explicit
sample-dependent budget
`uniformRowSampleGramFullFpPerturbBudget`. The library also exposes a fixed
deterministic-radius transfer: if a scalar `τ` dominates that budget for every
joint preprocessing/sampling outcome, then the same probability lower bound
holds with radius `ε + τ`. A row-norm cap on every sampled row gives the
concrete domination
`uniformRowSampleGramFullFpPerturbBudget <= uniformRowSampleGramFullFpConstBudget fp s (m * R)`.
The library now also proves the source-sharp SRHT row-norm route in explicit
`t` form. The positive-flip self-bounding estimate feeds a finite-cube
exponential-tilt bridge, yielding the one-row tail
`exp (-m t^2 / 8)`, the all-row row-norm cap
`sqrt(n / m) + t`, and the induced leverage cap
`(sqrt(n / m) + t)^2 / n` with failure budget
`m * exp (-m t^2 / 8)`. This sharper preprocessing event is composed with the
iid uniform row-sampling matrix-concentration theorem on the product law,
giving an exact two-sided sample-Gram theorem with probability at least
`1 - (deltaPre + deltaSample)`. The logarithmic source-constant wrapper is now
formalized as well: choosing `t = sqrt (8 * log (m / deltaPre) / m)` makes the
preprocessing failure budget exactly `deltaPre`. The coordinate-Hoeffding route
remains as a weaker fully proved alternative. The matching source-sharp
floating-point transfer is also formalized with the fixed budget
`uniformRowSampleGramFullFpConstBudget fp s (m * S^2)`, derived from the same
SRHT row-norm event rather than assumed globally.

```lean
#check preconditionRows
#check preconditionColumns
#check preconditionElements
#check preconditionRows_frobNorm_orthogonal
#check preconditionColumns_frobNorm_orthogonal
#check preconditionElements_frobNorm_orthogonal
#check preconditionRows_hasOrthonormalColumns_of_orthogonal
#check preconditionColumns_hasOrthonormalColumns_of_orthogonal
#check preconditionElements_hasOrthonormalColumns_of_orthogonal
#check rowSqNormProbDen_preconditionRows_eq_nat_of_orthogonal
#check rowSqNormProbDen_preconditionColumns_eq_nat_of_orthogonal
#check rowSqNormProbDen_preconditionElements_eq_nat_of_orthogonal
#check IsOrthogonal.diagMatrix_of_sq_eq_one
#check signedOrthogonalPreconditioner_isOrthogonal
#check signedOrthogonalPreconditionRows_hasOrthonormalColumns
#check rowSqNormProbDen_signedOrthogonalPreconditionRows_eq_nat
#check RademacherTrace
#check rademacherSign
#check rademacherSignVector_sq
#check rademacherTraceFlip
#check rademacherSignVector_flip_self
#check rademacherSignVector_flip_of_ne
#check rademacherSignVector_sub_flip
#check rademacherTraceProbMass_snoc
#check rademacherTraceFlip_involutive
#check rademacherTraceFlipEquiv
#check rademacherTraceProbMass_flip
#check rademacherTraceProbability_expectationReal_flip
#check rademacherTraceProbability_expectationReal_succ_last_eq
#check rademacherTraceProbability_expectationReal_succ_eq_prod
#check rademacherTraceProbability_entropyReal_succ_eq_prod
#check rademacherTraceFlip_castSucc_snoc
#check rademacherTraceFlip_last_snoc
#check rademacherTraceProbability_entropyReal_sq_le_sum_flip
#check rademacherTraceProbability_flip_tilt_sq_sum_le_of_pointwise_pair_le
#check rademacherTraceProbability_flip_tilt_sq_sum_bound_of_pointwise_pair_le
#check rademacherTraceProbability_flip_tilt_sq_sum_bound_of_pointwise_halfdiff_sq_le
#check rademacherTraceProbability_flip_tilt_sq_sum_bound_of_pointwise_absdiff_le
#check rademacherTraceProbability_entropyReal_exp_mul_le_of_flip_tilt_sq_sum_bound
#check rademacherTraceProbability_eventProb_real_le_mean_add_ge_one_sub_exp_sq_of_flip_tilt_sq_sum_bound
#check rademacherTraceProbability_expectationReal_sign_eq_zero
#check rademacherTraceProbability_expectationReal_sign_mul_eq_ite
#check rademacherTraceProbability_expectationReal_sq_sum_mul_sign_eq_sum_sq
#check rademacherTraceProbability_expectationReal_exp_sum_mul_sign_eq_prod
#check rademacherTraceProbability_eventProb_sum_mul_sign_le_ge_one_sub_exp_mul_prod
#check real_rademacher_cosh_factor_le_exp_sq_div_two
#check rademacherTraceProbability_expectationReal_exp_sum_mul_sign_le_exp_sum_sq_div_two
#check rademacherTraceProbability_expectationReal_exp_lam_sum_mul_sign_le_exp_lam_sq_sum_sq_div_two
#check rademacherTraceProbability_eventProb_sum_mul_sign_ge_le_exp_sq_bound
#check rademacherTraceProbability_eventProb_sum_mul_sign_le_ge_one_sub_exp_sq_bound
#check rademacherTraceProbability_eventProb_abs_sum_mul_sign_le_ge_one_sub_two_mul_exp_sq_bound
#check rademacherTraceProbability
#check HadamardFlat
#check signedHadamardPreconditionRows_entry
#check signedHadamard_entry_coeff_sum_sq_eq_inv
#check signedHadamard_row_inner_sq_sum_eq_inv_mul
#check FiniteVecConvex
#check FiniteVecLipschitzWith
#check unitCubeToRademacherVec
#check finiteVecConvex_scaled_unitCubeToRademacher
#check finiteVecLipschitzWith_scaled_unitCubeToRademacher
#check vecNorm2_linear_combination_convex
#check signedHadamard_row_vecNorm2_convex
#check hasOrthonormalColumns_vecNorm2Sq_mul_vec_eq
#check hasOrthonormalColumns_transpose_mul_vecNorm2Sq_le
#check abs_vecNorm2_sub_le_vecNorm2_sub
#check signedHadamard_row_vecNorm2_lipschitz
#check signedHadamard_row_vec_sub_flip
#check signedHadamard_row_vecNorm2_positive_flip_sq_sum_le
#check rademacherTraceProbability_flip_tilt_sq_sum_bound_signedHadamard_row_vecNorm2
#check rademacherTraceProbability_eventProb_vecNorm2_signedHadamard_le_mean_add_ge_one_sub_exp_m_t_sq_div_eight
#check rademacherTraceProbability_eventProb_entry_abs_signedHadamard_le_ge_one_sub_exp_sq_bound
#check rademacherTraceProbability_eventProb_forall_entry_abs_signedHadamard_le_ge_one_sub_sum_exp_sq_bound
#check rademacherTraceProbability_expectationReal_rowNormSq_signedHadamard_eq
#check rademacherTraceProbability_expectationReal_sqrt_rowNormSq_signedHadamard_le
#check rademacherTraceProbability_eventProb_forall_vecNorm2_signedHadamard_le_sqrt_add_ge_one_sub_m_exp_m_t_sq_div_eight
#check rademacherTraceProbability_eventProb_forall_rowNormSq_signedHadamard_le_sqrt_add_sq_ge_one_sub_m_exp_m_t_sq_div_eight
#check rademacherTraceProbability_eventProb_forall_rowNormSq_signedHadamard_le_log_delta_ge_one_sub_delta
#check rademacherTraceProbability_eventProb_forall_leverageScoreProb_signedHadamard_le_sqrt_add_sq_div_nat_ge_one_sub_m_exp_m_t_sq_div_eight
#check rademacherTraceProbability_eventProb_forall_leverageScoreProb_signedHadamard_le_sqrt_add_sq_div_nat_ge_one_sub_delta
#check rademacherTraceProbability_eventProb_forall_leverageScoreProb_signedHadamard_le_log_delta_ge_one_sub_delta
#check rademacherTraceProbability_eventProb_rowNormSq_signedHadamard_le_ge_one_sub
#check rademacherTraceProbability_eventProb_forall_rowNormSq_signedHadamard_le_ge_one_sub
#check rademacherTraceProbability_eventProb_forall_rowNormSq_signedHadamard_le_ge_one_sub_delta
#check rademacherTraceProbability_eventProb_forall_rowNormSq_signedHadamard_le_ge_one_sub_sum_exp_sq_bound
#check rademacherTraceProbability_eventProb_forall_leverageScoreProb_signedHadamard_le_ge_one_sub_sum_exp_sq_bound
#check rademacherTraceProbability_eventProb_forall_leverageScoreProb_signedHadamard_le_ge_one_sub_delta
#check uniformRowOuterGramSample
#check finiteQuadraticForm_uniformRowOuterGramSample_eq
#check finitePSD_uniformRowOuterGramSample
#check uniform_rowOuterGramSample_mean_eq_id
#check uniformRowOuterGramSample_finiteLoewnerLe_of_leverageScoreProb_le
#check rademacherTraceProbability_eventProb_forall_uniformRowOuterGramSample_signedHadamard_finiteLoewnerLe_ge_one_sub_delta
#check uniformRowProb
#check uniformRowTraceProbability
#check uniformRowSampleGram
#check uniformRowSampleGram_sub_finiteIdMatrix_eq_centered_average
#check uniformRowOuterGramSample_centered_square_expectationCStarMatrix_le
#check uniformRowTraceProbabilityFiniteRealTraceMGFLogBound_centered_le
#check uniformRowTraceProbabilityFiniteRealTraceMGFLogBound_neg_centered_le
#check uniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_tail_budget
#check signedHadamardUniformRowTraceProbability
#check signedHadamardUniformRowSampleGramTwoSidedEvent
#check signedHadamardUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta
#check signedHadamardUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht
#check signedHadamardUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
#check uniformRowSampleGramFullFpConstBudget
#check uniformRowSampleGramFpPerturbConstBudget_eq_nat_mul
#check uniformRowSampleGramDotProductConstBudget_eq_nat_mul
#check abs_mul_entry_le_rowNormSq
#check uniformRowSampleSketch_abs_mul_sum_le_of_rowNormSq_le
#check uniformRowSampleGramFullFpPerturbBudget_le_const_of_sample_rowNormSq_le
#check signedHadamardFlUniformRowSampleGramTwoSidedConstBudgetEvent
#check signedHadamardUniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_constBudget
#check signedHadamardUniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_constBudget_srht
#check signedHadamardUniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_constBudget_srht_log_preprocess
#check rademacherTraceProbability_eventProb_signedOrthogonalPreconditionRows_eq_one
#check fl_preconditionRows_error_bound
#check fl_preconditionColumns_error_bound
#check fl_preconditionElements_error_bound
```

Paper-level RandNLA scope is summarized in this README by the Algorithm 1--3
sections and the later least-squares and low-rank sections, with shipped checked
names indexed in [`docs/LIBRARY_LOOKUP.md`](docs/LIBRARY_LOOKUP.md). Historical
external ledgers and PDF summaries are not part of the current repository; use
the checked theorem surfaces here as the repository-visible source of truth.

## RandNLA Least-Squares Sketches

For equation (8), the repository now formalizes the deterministic
least-squares implication used by sketching algorithms. If a sketched problem
preserves every squared residual objective within factors `1 ± ε`, then an
exact minimizer of the sketched problem has original squared residual at most
`(1 + ε) / (1 - ε)` times the residual of any comparison vector, including an
exact minimizer of the original problem. The module also includes the
probability bridge from a preservation event to the randomized sketched
minimizer guarantee. For leverage-score row sampling, both the older
operator-event route and the sharper equation (7) finite-Loewner Bennett
sample-budget event now plug into this bridge, in exact and fully
floating-point Gram forms. The exact row-sampled least-squares matrix/vector
with leverage scaling is also represented concretely. The literal rounded
row-sampled matrix/vector construction is also modeled by applying the local
division FP primitive to every sampled/scaled row entry, and the repository now
proves both the corresponding rowwise residual perturbation bound and its
deterministic squared-objective perturbation lift. These rounded residual
theorems are real implementation foundations, but they are not advertised as
the older rounded-Gram hypothesis: separately rounding `A` and `b` creates
additional residual/objective perturbation terms. The current high-probability
literal-rounded theorem composes those terms with the exact finite-Loewner
sketch event under an explicit objective-budget condition at the rounded
minimizer and at `xOpt`; it does not assume that budget silently. The same
support-aware high-probability transfer is now available for an additive-gap
approximate minimizer of the literal rounded sampled problem, with the solver
objective gap explicitly added to the required slack budget. This closes the
objective-gap bridge needed by downstream solvers. The repository also proves
a forward-error version: a componentwise bound on the solver output's distance
from an exact rounded minimizer induces the needed objective gap through an
explicit residual budget. A new perturbed-Gram-system adapter reuses the local
least-squares forward-error theorem to construct that componentwise certificate
from explicit perturbations of the rounded normal equations. A further QR
least-squares-spec adapter consumes the local `LSQRSolveBackwardError`
structure by converting its Frobenius Gram perturbation radius to entrywise
radii; it still does not prove that a concrete QR/preconditioner produces that
structure. A new rectangular-normal-equation adapter now narrows that remaining
QR obligation: a future rectangular QR backward-error theorem only has to
provide perturbed rectangular normal equations and rectangular data
perturbation bounds; the new rectangular orthogonal one-step and multi-step
accumulation lemmas now prove the source-style perturbation update for
`m × n` data, with the multi-step theorem using the rigorous geometric radius
`((1+c)^r - 1) ||A||_F`. The matching vector accumulation lemmas now prove the
same source-style update for the transformed right-hand side `b`, with
Euclidean radius `((1+c)^r - 1) ||b||_2`. The simultaneous matrix/vector
accumulation theorem strengthens this to one common accumulated orthogonal
factor `Q`, which is the shape needed by the QR least-squares handoff. The
induced perturbation-budget lemmas then expand and bound the resulting
Gram/RHS perturbations, and
`LSQRSolveBackwardError.of_rectangular_perturbed_normal_equations` will feed
the resulting radii into the existing solver transfer. The normal-equation
handoff is also formalized: applying the same orthogonal row transformation to
the rectangular data matrix and right-hand side preserves the least-squares
normal equations. The top-block solve handoff is formalized as well: if the
transformed data has shape `[R;0]` and the computed vector solves the top
system `Rx=c`, then it satisfies the transformed rectangular normal equations,
with no zero assumption on the lower transformed right-hand side. This has also
been connected to the repository's floating-point back-substitution theorem:
`fl_backSub` solves a perturbed top system `(R+Delta R)x=c` with
`|Delta R| <= gamma_n |R|`, so the perturbed transformed top block satisfies
the rectangular normal equations. This perturbation is also pulled back through
the shared QR orthogonal factor: if `A_hat = Q^T(A+Delta A)` and
`b_hat = Q^T(b+Delta b)`, then the top-block perturbation gives original
perturbed data with `Delta A_total = Delta A + Q[Delta R;0]` and
`||Delta A_total||_F <= ||Delta A||_F + ||[Delta R;0]||_F`. The embedded
top-block norm is now discharged from the triangular-solve componentwise
budget, giving the strengthened radius
`||Delta A_total||_F <= ||Delta A||_F + gamma_n ||[R;0]||_F`. This now feeds
the local `LSQRSolveBackwardError` specification for any supplied common-`Q`
or supplied orthogonal-sequence rectangular QR route satisfying the final
`[R;0]` shape, transformed top RHS, and displayed norm-budget hypotheses.
This still deliberately stops short of a concrete `fl_householder_qr`
implementation theorem. The route-A exact Householder substrate now also
contains zero-prefix reflector lemmas: a full-size Householder reflector whose
Householder vector has a zero prefix has identity rows and columns on that
prefix, and therefore preserves those vector entries and matrix rows under
left application. These lemmas are the embedded trailing-reflector facts needed
before a concrete rectangular Householder QR implementation can prove that
finished rows/columns remain untouched. The next exact Householder dependency
is also closed: for the constructed active vector `v = x - alpha e_p` with
`alpha^2 = ||x||_2^2` and `v^T v != 0`, the exact reflector maps `x` to
`alpha e_p`, so every off-pivot active-column entry is zero. The QR-specific
trailing version is now formalized as well: `householderTrailingActiveVector`
has the required zero prefix, preserves the entries above the pivot, and zeros
the entries below the pivot when `alpha^2` is the squared norm of the trailing
segment. The theorem `exact_trailing_householder_sequence_lower_zero` proves
the exact lower-trapezoidal zero invariant for a supplied exact trailing
Householder recurrence, and `rectangular_topBlock_shape_facts_of_lower_zero`
turns that invariant into the solver-facing `[R;0]`, `cTop`, and
upper-triangular facts. The nonzero diagonal/rank condition is still explicit.
The rounded storage-shape part is now separated from the perturbation theorem:
`fl_householderStoredPanelStep` models a compact rounded panel update that
preserves completed columns and explicitly writes zeros below the active pivot,
and `fl_householderStoredPanel_sequence_topBlock_shape_facts` proves the final
stored `[R;0]`, top-RHS, and upper-triangular facts for such a loop. This does
not by itself prove that pivots are nonzero. The stored-step perturbation
contract is now also formalized:
`fl_householderStoredPanelStep_HouseholderColumnwisePanelAppError_of_budget`
shows that the stored panel/RHS step satisfies the source-faithful columnwise
Householder contract whenever the exact reflector preserves completed columns
and RHS prefix entries, zeros the stored pivot entries, and the compact-update
budgets are dominated by the chosen relative constant. Those preservation and
zeroing hypotheses are explicit. The one-step trailing-reflector theorem
`fl_householderStoredTrailingPanelStep_HouseholderColumnwisePanelAppError_of_budget`
now discharges those preservation, RHS-prefix, and pivot-zeroing hypotheses
from the pre-step lower-zero invariant and the exact trailing Householder
vector algebra. The multi-step loop theorem
`fl_householderStoredTrailingPanel_rect_orthogonal_columnwise_vector_sequence_geometric`
then invokes this one-step theorem at every pivot, using the stored lower-zero
invariant, and produces one accumulated orthogonal factor with columnwise data
and RHS perturbation radii. The final Higham-style factorization assembly
`fl_householderStoredTrailingPanel_higham_columnwise_factorization` now combines
that perturbation theorem with the stored `[R;0]`/top-RHS/upper-triangular shape
facts for the same concrete loop; it intentionally leaves nonzero diagonal and
conditioning hypotheses as separate solver-side obligations. The stored-loop
solver handoff is now closed by
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget`:
it reads the final `R` and `cTop` directly from `A_hat n` and `b_hat n`,
reuses the Higham columnwise factorization assembly theorem, and produces the local
`LSQRSolveBackwardError` certificate for `fl_backSub`. The diagonal condition
has also been narrowed by
`fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_budget_lt_abs_alpha`
and
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_pivot_error_lt_abs_alpha`:
if every pivot's componentwise compact-update budget is strictly smaller than
the exact Householder pivot magnitude `|alpha_k|`, then the final stored top
block has nonzero diagonal and the same solver certificate follows. The
Householder denominator condition is also narrowed to the scalar pivot
nonbreakdown condition `A_hat[k,k] != alpha_k` by
`householderTrailingActiveVector_inner_self_ne_zero_of_pivot_ne_alpha` and the
stored-loop wrapper
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_pivot_ne_alpha_and_pivot_error_lt_abs_alpha`.
That scalar condition is further reduced to the standard Householder sign
choice plus positive trailing-column norm by
`householder_pivot_ne_alpha_of_trailingNorm2Sq_pos_mul_nonpos`,
`fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_trailingNorm_pos_mul_nonpos`,
and
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_trailingNorm_pos_mul_nonpos_and_pivot_error_lt_abs_alpha`.
The sign convention itself is now explicit:
`signedHouseholderAlpha` chooses the sign opposite to the pivot entry, while
`signedHouseholderAlpha_sqrt_trailingNorm2Sq_sq` and
`signedHouseholderAlpha_sqrt_trailingNorm2Sq_mul_pivot_nonpos` prove the
squared-norm and sign hypotheses from that definition. The Cox--Higham
pivoted/sorted weighted least-squares route now has its first local dependency:
`householderTrailingActiveVector_inner_self_ge_two_trailingNorm2Sq_of_mul_nonpos`
and `householderTrailingActiveVector_inner_self_ge_two_trailingNorm2Sq_signed`
prove the signed Householder denominator lower bound
`2 ||x_tail||_2^2 <= v^T v`, corresponding to Cox--Higham Lemma 2.1 before
column-pivoting and row-sorting estimates are applied.
The column-pivoting layer is also now local:
`exists_householderTrailingColumnNorm2Sq_active_max` chooses a remaining column
with maximal active trailing norm, while
`abs_inner_householderTrailingActiveVector_column_le_vecNorm2_mul_sqrt_of_pivot_max`
turns that pivot-max property and Cauchy--Schwarz into the active-column
comparison \(|v^T y_{\mathrm{tail}}|\le \|v\|_2\|x_{\mathrm{tail}}\|_2\).
The Cox--Higham Lemma 2.1 scalar endpoint is now formalized by
`abs_householderBeta_mul_inner_column_le_sqrt_two_of_signed_pivot_max`, which
combines the denominator and column-pivot comparisons to prove
`|beta * v^T y_tail| <= sqrt 2`; the follow-up row-growth theorem
`abs_householder_signed_pivot_update_entry_le_one_add_sqrt_two_mul_row_bound`
records the source estimate behind equation (4.3),
`|a_ij - phi*a_ik| <= (1 + sqrt 2) B`, under a row-entry bound `B`.
The row-sorting accumulation dependency is also local:
`scalar_growth_iterate_bound` proves repeated scalar growth by induction,
`coxHigham_rowSorting_active_entry_bound_of_prior_growth` applies the sorted
initial row bounds to an active row, and
`coxHigham_rowSorting_active_entry_bound_of_stage_growth` combines the two to
show that \(k\) prior growth steps bounded by \(1+\sqrt 2\) yield
`|A_k(r,j)| <= (1 + sqrt 2)^k row0Bound(k)` for sorted active rows `r >= k`.
The pivot-row part of Cox--Higham equations (4.4)--(4.5) is represented by
`vecNorm2_le_sqrt_card_mul_of_abs_le`,
`coxHigham_pivot_row_entry_bound_of_active_tail_entry_bound`, and
`coxHigham_pivot_row_entry_bound_of_stage_entry_bound`: these turn an
active-tail column-norm bound plus an active-tail entrywise row bound into the
explicit pivot-row factor `sqrt m * B`.  This uses the repository's ambient
`Fin m` norm, so the sharper source factor `sqrt (m-k+1)` remains a possible
refinement rather than a hidden claim.  The exact signed-reflector pivot-row
bridge is now also local: `householderBeta_mul_inner_self_eq_two` exposes the
normalization needed for orthogonality,
`abs_matMulVec_householder_pivot_le_trailing_vecNorm2_of_zero_prefix_orthogonal`
bounds a zero-prefix orthogonal Householder update at the pivot row by the
active-tail norm, and
`coxHigham_exact_signed_pivot_row_entry_bound_of_stage_entry_bound` composes the
signed-pivot nonbreakdown, that active-tail estimate, and the row-sorted entry
budget into the source-shaped exact pivot-row bound.  This is still a scoped
route dependency, not the final QR/preconditioner theorem.
The row-wise additive perturbation accumulation needed by the same route is
also formalized: `scalarAffineGrowthBudget` and
`scalar_affine_growth_iterate_bound` package the recurrence
`M(t+1) <= c M(t) + eta(t)`,
`coxHigham_rowwise_error_accumulation_bound` applies it to computed/exact
row-entry discrepancies, and
`coxHigham_rowSorting_active_entry_bound_with_accumulated_error` combines the
exact row-sorting bound with the accumulated row-wise error.
The concrete stored rounded panel loop now supplies this additive term:
`fl_householderStoredPanelStep_active_entry_componentwise_error_bound`
specializes the stored-step componentwise budget to an active row/column entry,
`coxHigham_storedPanelStep_row_error_recurrence_of_exact_lipschitz` turns the
same-step exact Cox--Higham Lipschitz field into one affine row-error step, and
`coxHigham_storedPanel_sequence_rowwise_error_accumulation_bound_of_exact_lipschitz`
iterates the concrete compact Householder budgets through
`scalarAffineGrowthBudget`.  The cleaner source-shaped row-magnitude adapter is
also formalized: `coxHigham_storedPanelStep_active_entry_bound_of_exact_growth`
and `coxHigham_storedPanel_sequence_active_entry_bound_of_exact_growth` state
that exact same-reflector Cox--Higham row growth for the current stored panel
plus the concrete compact FP component budget gives the rounded row-magnitude
recurrence directly.  This avoids treating the older exact-sequence adapter as
a proof of the remaining exact pivoted/sorted loop field.  The first exact
bridge into that visible field is now formalized too:
`matMulVec_householder_signed_pivot_update_entry_eq` rewrites the Householder
matrix-vector update as the Cox--Higham scalar row update for non-pivot active
rows, and
`coxHigham_exact_same_reflector_row_growth_of_signed_pivot_row_bound` applies
the signed column-pivot row-growth estimate directly to that exact
same-reflector term.  The route now also has a one-step active-row case split:
`coxHigham_exact_signed_pivot_active_row_entry_bound_of_stage_bounds` uses the
non-pivot scalar bridge below the pivot and the exact pivot-row active-tail
bridge at the pivot, with the honest unified factor
`max (1 + sqrt 2) (sqrt m)`.
The exact multi-stage bridge is now represented by a concrete signed-pivot
Householder panel step:
`exactSignedPivotHouseholderPanelStep`,
`coxHigham_exactSignedPivotPanelStep_active_entry_bound_of_stage_bounds`,
`coxHigham_exactSignedPivotPanelStep_active_block_bound_of_stage_bound`,
`coxHigham_exactSignedPivotPanel_sequence_active_entry_bound_of_stage_budgets`,
`coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_stage_budgets`,
and
`coxHigham_exactSignedPivotPanel_sequence_active_entry_bound_of_geometric_stage_budgets`,
plus the active-block geometric wrapper
`coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_geometric_stage_budgets`.
These theorems propagate visible Cox--Higham stage budgets through the exact
pivoted/sorted loop object.  The active-block wrapper shows that one uniform
active-block bound supplies the separate row and column stage fields in the
one-step theorem, and the active-block sequence wrappers replace the separate
row/column stage fields by one active-block family at every stage.  The
monotone-window propagation theorem
`coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound`
then proves that active-block family from an initial entrywise bound, assuming
the active row/column windows move monotonically and the visible positive-norm
and pivot-max fields hold at each stage.
The positive-norm field has also been reduced:
`householderTrailingColumnNorm2Sq_pos_of_pivot_max_exists_pos` and
`householderTrailingColumnNorm2Sq_pos_of_pivot_max_exists_active_entry_ne`
show that pivot maximality plus positive active mass in some remaining column
forces the chosen pivot column to have positive active norm, and
`coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_active_block_nonzero`
uses this to replace the direct sequence-level positive-norm hypothesis by a
remaining-active-block nonzero witness.
The pivot-max field now has an explicit finite selector as well:
`householderActiveMaxPivotColumn`, `householderActiveMaxPivotColumn_ge`, and
`householderActiveMaxPivotColumn_pivot_max`; the sequence wrapper
`coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_active_max_pivot`
uses the policy equation that the current pivot column is this selector, so the
raw pivot-max inequality is no longer a theorem input in that wrapper.
The active-nonzero witness can now be supplied by a scalar active-block mass:
`householderActiveBlockNorm2Sq` measures the squared Frobenius mass of the
remaining active block, and
`exists_active_entry_ne_of_householderActiveBlockNorm2Sq_pos` turns positivity
of that mass into the explicit nonzero active entry consumed by the
Cox--Higham nonbreakdown bridge.  The exact sequence wrapper
`coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_active_block_norm_pos`
therefore replaces the existential active-nonzero field by positive
active-block mass plus the active max-pivot policy.
The displayed pivot-policy field now has a concrete column-swap bridge:
`householderSwapColumns` swaps the selected active max column into the current
active position, `householderSwapColumns_activeMaxPivotColumn_pivot_max`
proves that the displayed post-swap column is pivot-maximal on the active
suffix, and
`coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_swapped_active_max_pivot`
feeds this post-swap policy into the exact active-block sequence theorem.  This
still leaves the positive active-block mass/nonbreakdown invariant and the
rounded solver connection as open QR/preconditioner obligations.
The mass condition is now pushed back through the same swap:
`householderActiveBlockNorm2Sq_pos_of_exists_active_entry_ne` gives the reverse
active-entry-to-mass direction,
`householderActiveBlockNorm2Sq_swapColumns_pos_of_pos` proves that swapping a
column inside the active suffix preserves positivity of the active-block mass,
and
`coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_swapped_active_max_pivot_of_raw_active_block_norm_pos`
lets the exact swapped-stage theorem assume raw-stage active-block
nonbreakdown instead of a separate post-swap mass condition.
The raw-stage mass condition is now connected to the existing QR
rank/nonbreakdown infrastructure:
`householderActiveBlockNorm2Sq_pos_of_column_notInPreviousSpan`,
`householderActiveBlockNorm2Sq_pos_of_leading_witnesses`,
`householderActiveBlockNorm2Sq_pos_of_leading_block_leftInverses`, and
`householderActiveBlockNorm2Sq_pos_of_leading_block_det_ne_zero`
turn the repository's previous-span, local-inverse, and determinant
nonbreakdown routes into positive active-block mass.  The stagewise wrapper
`householderActiveBlockNorm2Sq_pos_sequence_of_leading_block_det_ne_zero`
packages this for stored QR stages under visible previous/current
leading-block determinant hypotheses and the stored lower-zero shape.
The stored-panel
floating-point handoff now accepts this honest active-row factor:
`coxHigham_storedPanelStep_active_entry_bound_of_exact_growth_factor` and
`coxHigham_storedPanel_sequence_active_entry_bound_of_exact_growth_factor`
parameterize the rounded row-magnitude recurrence by an arbitrary nonnegative
exact growth factor, while
`coxHigham_storedPanel_sequence_active_entry_bound_of_exact_active_growth`
specializes it to `coxHighamActiveRowGrowthFactor m`.  The newer
stage-budget handoff matches the exact signed-pivot sequence more directly:
`coxHigham_storedPanelStep_active_entry_bound_of_exact_stage_budget_factor`
and
`coxHigham_storedPanel_sequence_active_entry_bound_of_exact_stage_budgets_factor`
take an explicit source budget `B t`, while
`coxHigham_storedPanel_sequence_active_entry_bound_of_exact_active_stage_budgets`
uses the honest active-row factor.  Finally,
`coxHigham_storedPanelStep_active_entry_bound_of_signed_pivot_stage_bounds`
composes the exact signed-pivot one-step theorem with the concrete stored-panel
FP component budget.  These remain route dependencies: the concrete sorting
policy still has to propagate the visible active-block/stage-budget fields before the final
QR/preconditioner theorem can close.
The stored signed-pivot loop now also has a direct active-block recurrence:
`signedPivotHouseholderVector` and `signedPivotHouseholderBeta` package the
concrete reflector fields, and
`coxHigham_storedPanel_sequence_active_block_bound_of_signed_pivot_stage_bounds`
propagates rounded budgets `B_t` through the stored panel under visible
positive-pivot-norm, pivot-maximality, completed-column, pivot-column, monotone
active-window, and compact-budget recurrence assumptions.  This closes the
rounded active-block propagation dependency, while the final concrete loop must
still supply the leading-block determinant/lower-zero fields and connect the
rounded active-block recurrence to the QR/preconditioner solve theorem.
The QR and
least-squares wrappers
`fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_signed_alpha_trailingNorm_pos_sqrt_budget`,
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_signed_alpha_trailingNorm_pos_and_sqrt_budget`,
and
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_signed_alpha_prefix_lower_zero_triangular_leading_blocks_kappaInf_selfNorm_budget`
therefore remove the independent sign-choice hypothesis when the concrete
signed-alpha rule is part of the stored QR loop.
The prefix-local diagonal bridge
`fl_householderStoredPanel_sequence_prefix_diag_nonzero_of_step_diag_nonzero`
and its signed-alpha trailing-loop specialization
`fl_householderStoredTrailingPanel_sequence_prefix_diag_nonzero_of_signed_alpha_trailingNorm_pos_sqrt_budget`
show that previously written pivots remain nonzero at every intermediate
stored-loop step.  The solver wrapper
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_signed_alpha_prefix_lower_zero_pivot_nonzero_kappaInf_selfNorm_budget`
uses this to replace previous local diagonal assumptions by a loop-derived
fact, leaving only the current local pivot nonzero condition visible.
The nonsingular-leading-block solver wrapper
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_leading_block_det_ne_zero_sqrt_budget`
pushes the determinant/rank route all the way into the local QR solver
certificate: nonzero previous/current leading-block determinants plus the QR
lower-zero shape give positive trailing norm, and the square-root pivot budget
gives the concrete pivot-error inequality.
The triangular-leading-block solver wrapper
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_triangular_leading_blocks_sqrt_budget`
composes this with the triangular determinant adapters: visible upper-triangular
shape, previous/current leading diagonal nonzeros, sign choice, square-root
pivot budgets, compact update budgets, and final Gram/RHS budgets imply the
local `LSQRSolveBackwardError` certificate. The explicit-budget wrapper
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitNormBudget_of_signed_alpha_prefix_lower_zero_pivot_nonzero_kappaInf_selfNorm_budget`
uses the concrete radii `qrSolveFinalGramBudget` and
`qrSolveFinalRhsBudget`, so no separate final Gram/RHS domination hypotheses
are needed in that route. The stronger explicit-compact wrapper
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_pivot_nonzero_kappaInf_selfNorm_budget`
also chooses the compact-update domination constant internally as
`storedQRCompactSequenceRelativeBudget`, built from the repository's
componentwise compact Householder budgets. The QR layer also proves
`storedQRCompactSequenceRelativeBudget_le_mul_of_step_le`: a uniform per-step
relative cap `cStep` gives the global sequence cap `n * cStep`. It now also
proves `storedQRCompactStepRelativeBudget_le_mul_add_of_column_rhs_le`, reducing
one stored step to vector-level relative compact caps `n * cCol + cRhs`.
The norm-budget companion
`storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_columnRhsNormBudget_le`
starts one level earlier: primitive compact Householder norm budgets bounded by
`cCol * ||A_k(:,j)||_2` and `cRhs * ||b_k||_2` are converted to those relative
caps by `householderCompactRelativeBudget_le_of_normBudget_le_mul`. The solver
now also exposes the componentwise companion
`storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_columnRhsComponentBudget_le`:
component budgets bounded by `cCol * |A_k(i,j)|` and `cRhs * |b_k(i)|` first
give the norm-budget caps via
`householderCompactNormBudget_le_mul_of_componentBudget_le_mul_abs`.  Since
that entrywise-relative cap is too strong for zero or tiny entries in a
nonlocal Householder update, the library also proves the valid primitive
norm-coefficient route:
`householderCompactNormBudget_le_normBudgetCoeff_mul`,
`storedQRCompactStepRelativeBudget_le_mul_add_normBudgetCoeff`, and
`storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_normBudgetCoeff_le`.
This route bounds the explicit compact arithmetic by a reflector-dependent
coefficient `householderCompactNormBudgetCoeff` times the input norm.  The
finite-max companion `storedQRCompactStepNormBudgetCoeffBudget` canonically
chooses the maximum of those stage coefficients, and
`storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_normBudgetCoeffBudget`
uses that displayed max directly in the scalar compact-product condition. The solver
wrapper
`storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_columnRhsBudget_le`
uses the explicit sequence cap `n * (n * cCol + cRhs)` in the finite-maximum
product condition. This removes the separate compact-update budget hypotheses
when those vector-level caps, componentwise caps, or reflector-coefficient caps
and the scalar smallness inequality are supplied.
The norm-square-budget variant
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_pivot_nonzero_kappaInf_selfNorm_normSqBudget`
also replaces the visible square-root pivot-budget hypothesis by the
dimensioned margin `m * budget_k^2 < ||A_k(k:m,k)||_2^2`, deriving the
square-root form internally. These are intentionally visible-domain theorems,
not claims that generic full column rank forces every leading principal block
to be nonsingular.
The positive-norm and pivot-budget sides now have small scalar bridges:
`householderTrailingNorm2Sq_pos_of_exists_ne` converts a nonzero active
trailing-column entry into `0 < ||x_tail||_2^2`,
`householderTrailingNorm2Sq_pos_of_pivot_ne_zero` handles the pivot-entry
special case, and
`not_forall_trailingNorm2Sq_pos_implies_pivot_ne_zero` records the converse
failure: a positive trailing norm alone does not imply that the current
unpivoted pivot entry is nonzero.  The bridge
`householderTrailingNorm2Sq_pos_of_nonneg_budget_lt_sqrt`
proves that a nonnegative budget below the square root already implies
positive trailing norm, and
`budget_lt_abs_alpha_of_lt_sqrt_trailingNorm2Sq` rewrites a
square-root trailing-norm budget into the stored-loop condition
`budget_k < |alpha_k|`. The active-entry bridge
`budget_lt_sqrt_householderTrailingNorm2Sq_of_lt_abs_active_entry` now also
proves that a concrete bound `budget_k < |A_k(i,k)|` for some active
trailing row `i >= k` is enough to discharge the square-root norm budget.
The dimensioned norm-margin bridge
`exists_active_entry_budget_lt_abs_of_dim_mul_budget_sq_lt_trailingNorm2Sq`
is the next quantitative step: if
`m * budget_k^2 < ||A_k(k:m,k)||_2^2`, then some active trailing entry must
exceed the budget. The direct bridge
`budget_lt_sqrt_householderTrailingNorm2Sq_of_dim_mul_budget_sq_lt_trailingNorm2Sq`
also turns the same norm-square margin straight into the square-root budget
used by QR. This is not a conditioning theorem by itself, but it turns a future
trailing-norm lower bound into the budget form consumed by the stored
nonbreakdown route.
The first conditioning-style lower-bound bridge is now formalized as
`householderTrailingNorm2Sq_ge_inv_leading_dual_norm_budget`: if a
leading-column dual row has squared norm at most `K`, then prefix-span
nonbreakdown gives `1 / K <= ||A_k(k:m,k)||_2^2`.  The companion
`dim_mul_budget_sq_lt_trailingNorm2Sq_of_leading_dual_norm_budget` turns
`m * budget_k^2 < 1 / K` into the dimensioned norm-square margin above.
This still exposes the dual row and its norm budget; it does not yet derive
them from an SVD or condition-number theorem.
A local-inverse-row bridge is also available:
`vecNorm2Sq_qrLeadingRow_padded_eq` and
`qrLeadingColumnLeftInverse_padded_row_norm_sq_eq` prove that the zero-padded
dual row constructed from a leading-block left inverse has the same squared
norm as the corresponding local inverse row.
`householderTrailingNorm2Sq_ge_inv_leadingBlock_leftInverse_row_norm_budget`
and
`dim_mul_budget_sq_lt_trailingNorm2Sq_of_leadingBlock_leftInverse_row_norm_budget`
therefore replace the ambient dual-row norm hypothesis by a row-norm budget on
the local leading-block inverse. This still exposes the inverse row-norm budget
instead of deriving it from a condition-number theorem.
The source-faithful local inverse row route now also has explicit repository
budget wrappers for Frobenius and infinity inverse-norm budgets: these compose
the row/Frobenius/infinity norm bridges with `qrSolveFinalGramBudget`,
`qrSolveFinalRhsBudget`, and `storedQRCompactSequenceRelativeBudget`.
The first rank-route bridge is also now formalized:
`qrColumnNotInPreviousSpan` and
`qrPrefixSupportSpannedByPreviousColumns` express the local QR invariant that
the current pivot column is not generated by previous columns while the
already-finished columns span prefix-supported vectors.
The prefix-span half can now be generated from concrete leading-block basis
coefficients:
`qrPrefixBasisCoefficientMatrix` states that coefficients on the previous
columns reproduce the first `k` coordinate vectors, and
`qrPrefixBasisCoefficientMatrix_of_leftInverse_previousLeadingBlockTranspose`
produces such coefficients from a local `IsLeftInverse` witness for the
transposed leading block `qrPreviousLeadingBlockTranspose`.
`qrPrefixSupportSpannedByPreviousColumns_of_prefixBasisCoefficientMatrix`
turns this witness plus the QR lower-zero shape into
`qrPrefixSupportSpannedByPreviousColumns`.
The left-inverse-facing adapter
`qrPrefixSupportSpannedByPreviousColumns_of_leftInverse_previousLeadingBlockTranspose`
composes those two steps directly, and
`fl_householderStoredPanel_sequence_prefixSpan_of_leftInverse_previousLeadingBlockTranspose`
derives the required lower-zero shape from the stored panel recurrence.  This
closes the prefix-span subdependency for source-faithful QR routes that keep
previous leading-block left inverses visible.
The column-independence half can now be generated from a concrete leading
left-inverse.  The helper `qrLeadingBlock` names the concrete leading
`(k+1) x (k+1)` block, and
`qrLeadingColumnLeftInverse_of_leftInverse_leadingBlock` pads a local
`IsLeftInverse` witness for that block by zeros to obtain the ambient
left-inverse witness.
`qrLeadingColumnLeftInverse` states that this dual coefficient family selects
the first `k+1` columns, and
`qrColumnNotInPreviousSpan_of_leadingColumnLeftInverse` proves that the
current pivot column cannot lie in the span of previous columns.
The two halves can now be composed directly:
`exists_active_trailing_entry_ne_of_leading_witnesses` and
`householderTrailingNorm2Sq_pos_of_leading_witnesses` derive a nonzero active
trailing entry and positive trailing norm from the coefficient witness,
left-inverse witness, and QR lower-zero shape, while
`fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_leading_witnesses_sqrt_budget`
feeds those witnesses into the stored-loop diagonal theorem.
The local-inverse variant
`exists_active_trailing_entry_ne_of_leading_block_leftInverses`,
`householderTrailingNorm2Sq_pos_of_leading_block_leftInverses`, and
`fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_leading_block_leftInverses_sqrt_budget`
composes the two local `IsLeftInverse` block witnesses directly into that same
stored-loop diagonal theorem.
The determinant/rank variant now removes those raw inverse-witness hypotheses:
the shared matrix-algebra theorem `exists_isLeftInverse_of_det_ne_zero`
converts a nonzero Mathlib determinant into the repository's
`IsLeftInverse` predicate, while
`qrPrefixBasisCoefficientMatrix_of_det_ne_zero_previousLeadingBlockTranspose`,
`qrLeadingColumnLeftInverse_of_det_ne_zero_leadingBlock`,
`exists_active_trailing_entry_ne_of_leading_block_det_ne_zero`,
`householderTrailingNorm2Sq_pos_of_leading_block_det_ne_zero`, and
`fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_leading_block_det_ne_zero_sqrt_budget`
feed nonzero local leading-block determinants into the same stored QR
nonbreakdown route.
The next triangular determinant bridge is also formalized:
`det_ne_zero_of_upper_triangular_diag_ne_zero` and
`det_ne_zero_of_lower_triangular_diag_ne_zero` prove that triangular local
blocks with nonzero diagonal have nonzero determinant.  The converse direction
needed for the current structured pivot route is also available as
`diag_ne_zero_of_upper_triangular_det_ne_zero`: an upper-triangular finite real
matrix with nonzero determinant has nonzero diagonal entries.  The QR adapters
`qrPreviousLeadingBlockTranspose_det_ne_zero_of_local_lower_triangular_diag_ne_zero`
and
`qrLeadingBlock_det_ne_zero_of_local_upper_triangular_diag_ne_zero` expose the
source-local block conditions directly.  The ambient adapters
`qrPreviousLeadingBlockTranspose_det_ne_zero_of_upper_triangular_diag_ne_zero`
and `qrLeadingBlock_det_ne_zero_of_upper_triangular_diag_ne_zero` apply this
to the previous transposed leading block and current leading block.  This
does not claim generic full-column-rank nonbreakdown: the current leading
principal block route keeps the needed nonzero leading diagonal visible.  The
route-elimination theorem
`not_forall_det_ne_zero_implies_first_pivot_ne_zero` formalizes the reason:
the nonsingular `2 × 2` column-swap matrix has a zero first unpivoted pivot.
The strengthened route-elimination theorem
`not_forall_det_ne_zero_implies_all_leading_blocks_det_ne_zero` records the
same obstruction at the exact leading-principal-minor level: nonsingularity of
the whole unpivoted matrix does not imply nonsingularity of all leading QR
blocks.
The structured replacement is now also formalized:
`qrLeadingBlock_current_pivot_ne_zero_of_local_upper_triangular_det_ne_zero`
and
`fl_householderStoredTrailingPanel_sequence_current_pivot_ne_zero_of_leadingBlock_det_ne_zero`
derive the current pivot nonzero condition from a nonsingular local leading
block together with the stored lower-zero QR shape.  The solver wrapper
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_leadingBlock_det_ne_zero_kappaInf_selfNorm_normSqBudget`
therefore replaces the latest explicit compact QR certificate's bare current
pivot hypothesis by the structured local determinant hypothesis.  The stronger
wrapper
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget`
also removes the separate norm-square pivot-margin assumption: it derives that
margin from the same local leading determinant, the stored lower-zero shape,
the local `kappaInf` budget, and the displayed dual compact-budget inequality.
The companion direct inverse-budget wrapper
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_leadingBlock_det_ne_zero_invNorm_dualBudget`
removes the local `kappaInf` hypotheses from that latest route when the direct
budget `(k+1)||nonsingInv(S_k)||_∞^2 <= K_k` is available instead. It still
keeps the dual compact-budget inequality visible.
The diagonal-dominant companion
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_diagDominant_leadingBlock_det_ne_zero_dualBudget`
derives that direct inverse budget from the existing Higham triangular inverse
bound under local diagonal dominance, nonzero local leading determinant, and
the displayed diagonal-minimum budget.
The concrete-dual companion
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_diagDominant_leadingBlock_det_ne_zero_concreteDualBudget`
removes the arbitrary auxiliary `K_k`: it chooses
`K_k = 2 * D_k`, where `D_k` is the formal Higham diagonal-dominant inverse
budget, and replaces the two `K_k` hypotheses by the direct smallness condition
`m * B_k^2 < 1 / (2 * D_k)`.
The product-form companion
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_diagDominant_leadingBlock_det_ne_zero_concreteDualProductBudget`
uses the scalar bridge
`mul_sq_lt_inv_two_mul_of_two_mul_mul_sq_lt_one` to replace that denominator
condition by `2 * D_k * (m * B_k^2) < 1`, deriving all denominator positivity
from local diagonal dominance.
The stored-sequence companion
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_diagDominant_leadingBlock_det_ne_zero_concreteDualProductSequenceBudget`
replaces the raw pivot compact component `B_k` in that product by the
repository's deterministic stored QR compact sequence budget times the current
pivot-column norm, using
`storedQRCompactPivotBudget_le_sequence_column_norm` and
`two_mul_mul_sq_lt_one_of_nonneg_le`.
The scalar route-elimination theorem
`not_forall_pos_implies_two_mul_mul_sq_lt_one` records that `D_k > 0` alone
cannot imply this product smallness condition; a genuine compact-update budget
bound or domain assumption is still required.
The companion route-elimination theorem
`not_forall_diagDominantUpper_implies_two_mul_budget_expr_mul_sq_lt_one`
records that even local diagonal dominance and the displayed Higham budget do
not imply product smallness without a real compact-update budget bound.
The cross-route theorem
`not_forall_upper_tri_det_ne_zero_product_budget_implies_diagDominant` records
the converse obstruction: upper-triangular nonsingularity plus a satisfiable
product compact-smallness inequality still does not imply diagonal dominance.
The row-max analogue
`not_forall_upper_tri_det_ne_zero_product_budget_implies_rowMaxDiagDefectBudget_nonpos`
records that the same triangular nonsingularity plus satisfiable product
compact-smallness surface also does not imply nonpositive
`storedQRRowMaxDiagDefectBudget`; row-max control remains an independent
source/domain obligation.
The active-budget row-max strengthening
`not_forall_leadingBlock_upper_det_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_rowMaxDiagDefectBudget_nonpos`
shows that adding positive active-block mass, active max-pivoting, and
active/off-diagonal budget control to that product surface still does not
prove the row-max scalar defect condition.
The stage-diagonal analogue
`not_forall_upper_tri_det_ne_zero_product_budget_implies_stageDiagLowerDefectBudget_nonpos`
fixes the constant stage budget `2` and shows that the same surface also does
not imply `storedQRStageDiagLowerDefectBudget <= 0`; compact-product
smallness cannot replace the active/prefix diagonal lower-bound invariant.
The active-budget stage-diagonal strengthening
`not_forall_leadingBlock_upper_det_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_stageDiagLowerDefectBudget_nonpos`
shows that adding the active-pivot budget surface still does not prove the
scalar stage-diagonal lower-bound condition.
The active-budget comparison strengthening
`not_forall_leadingBlock_upper_det_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_stageBudget_le_rowMax`
shows that even adding product compact-smallness to the active-pivot
active/off-diagonal budget surface still does not imply the displayed
`stageBudget <= rowMax` comparison.
The conditioning-facing compact-smallness route elimination
`not_forall_upper_tri_det_ne_zero_kappaInf_bound_implies_two_mul_budget_expr_mul_sq_lt_one`
records the other missing direction: upper-triangular nonsingularity and a
finite local `κ∞` budget still do not imply product compact-smallness for an
arbitrary compact-update budget.
Both remaining assumptions need a genuine invariant or must stay visible.
The current proof-source checkpoint treats the remaining rectangular QR work as
a theorem-family choice: Higham's standard Householder QR theorem is
columnwise/normwise, while the Cox--Higham weighted least-squares result uses
row-wise bounds and requires pivoting or row sorting plus the correct sign
convention.  The library should not re-enter the diagonal-dominance/product
shortcut unless a new theorem supplies an actual compact-update budget.
The Cox--Higham route is now explicitly scoped as a separate future theorem
family rather than a drop-in closure for the current unpivoted stored-QR
preconditioner theorem: using it would change the algorithmic hypotheses to
include column pivoting plus row pivoting or row sorting and the specified
Householder sign convention.
As of the current bottleneck checkpoint, adjacent QR adapters are frozen unless
they either prove a stronger computed-loop/off-diagonal-control invariant,
or expose the remaining assumptions as domain hypotheses.
The route-elimination theorem
`not_forall_upper_tri_diag_nonzero_implies_diagDominant` records that upper
triangular shape plus nonzero diagonal alone cannot justify diagonal dominance:
the concrete matrix `[[1,2],[0,1]]` is the counterexample.
The determinant-facing companion
`not_forall_upper_tri_det_ne_zero_implies_diagDominant` records the same
obstruction for upper-triangular nonsingularity, using
`diagDominanceCounterexample2_det_ne_zero`.
The conditioning-facing companion
`not_forall_upper_tri_det_ne_zero_kappaInf_bound_implies_diagDominant` records
that even a visible finite `κ∞` certificate for the same nonsingular triangular
block does not imply diagonal dominance by itself; the positive QR route must
use a stronger computed-loop invariant or keep diagonal dominance visible.
The exact-QR-shape companion
`not_forall_orthogonal_upper_factorization_implies_diagDominant` records the
same obstruction even when the matrix is written as an exact orthogonal-times-
upper factorization with nonzero triangular diagonal, using
`A = I * [[1,2],[0,1]]`.  Thus the remaining positive route cannot rely on the
final QR shape alone; it needs a real off-diagonal-control invariant from the
computed loop.
The exact no-pivot Householder companion
`not_forall_exact_trailing_householder_sequence_implies_diagDominant` strengthens
that diagnosis: even the source-style exact trailing Householder recurrence,
with valid signed Householder squared norms and nonzero denominators, can
produce a final triangular factor whose first row violates diagonal dominance.
The concrete two-step witness starts from `[[1,2],[0,1]]` and ends with
`[[-1,-2],[0,-1]]`.  Therefore diagonal dominance is not a generic consequence
of the unpivoted Householder loop itself; it must come from an additional
off-diagonal-control hypothesis or remain visible as a domain assumption.
The strengthened route-elimination theorem
`not_forall_exact_trailing_householder_sequence_implies_diagDominant_and_property`
records the same obstruction for the paired finite-max route: no universal
exact-recurrence proof can produce diagonal dominance together with any extra
final-block property, including a scalar smallness side condition, without a
stronger invariant.
The stored-panel actual-unit strengthening
`not_forall_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_implies_diagDominant`
lifts this obstruction to the current stored-lower QR surface: an exact
floating-point model with `fp.u = 0`, the stored panel recurrence, the
signed-alpha equation, nonzero source denominators, and `(2 : ℝ) * fp.u < 1`
still reaches the same non-diagonally-dominant `2 x 2` final triangular block.
Thus local diagonal dominance or an equivalent off-diagonal-control invariant
cannot be recovered just by switching from the exact no-pivot recurrence to the
stored panel recurrence.
The same witness also rules out a hidden active-pivot-policy shortcut:
`not_forall_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_implies_activeMaxPivotChoice`
shows that the stored recurrence, signed-alpha equation, nonzero source
denominators, and actual-unit condition do not force the displayed pivot to be
`householderActiveMaxPivotColumn`; at stage zero the second column has larger
active trailing norm than the displayed first pivot.
The active-block route has the same limitation:
`not_forall_leadingBlock_upper_det_activeBlockPos_implies_offdiag_le_diag`
shows that upper-triangular nonsingular leading blocks plus positive
active-block mass still do not imply the row-wise off-diagonal domination
field required by `StoredQRSourceOffDiagonalControl`.  The same
`[[1,2],[0,1]]` witness has positive active-block mass and nonsingular leading
blocks but violates the first-row domination inequality.  Thus the new
rank/determinant-to-active-mass bridge cannot be treated as a hidden proof of
off-diagonal control.
The diagonal-lower-bound half of the Cox--Higham row-budget split is
independent as well:
`not_forall_leadingBlock_upper_det_activeBlockPos_offdiagBudget_implies_rowBudget_diag`
uses the same witness with row budget `2`.  The strict upper entry is bounded
by that budget, but the first displayed diagonal has magnitude `1`, so the
required lower bound `rowBudget <= |S_ii|` fails.  Row-growth upper bounds
therefore do not supply diagonal nonbreakdown by themselves; a final theorem
must prove a separate diagonal lower-bound invariant or keep it visible.
The active-pivot strengthening
`not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_offdiagBudget_implies_rowBudget_diag`
uses a first stage `[[2,1],[0,1]]` with an active max-pivot column and a second
stage `[[1,2],[0,1]]` with the same row-budget failure, so the active
max-pivot policy also cannot serve as the hidden diagonal lower-bound proof.
The active-block-budget strengthening
`not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_rowBudget_diag`
adds the hypothesis that the same budget controls the active trailing block at
each displayed stage.  The counterexample still fails at the same diagonal,
so active-block magnitude control plus active max-pivoting remains insufficient
for the diagonal lower-bound field.
The meta strengthening
`not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_property_implies_rowBudget_diag`
records that adding an arbitrary auxiliary side property true of the displayed
sequence and row budget also cannot rescue this route; the missing object is a
real diagonal lower-bound invariant, not another unrelated scalar side
condition.
The active-pivot row-max scalar route is independent for the same reason:
`activeMaxPivotRowBudgetDiagCounterexample_rowMaxDiagDefectBudget_pos` shows
the active-pivot witness has positive `storedQRRowMaxDiagDefectBudget`, and
`not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_rowMaxDiagDefectBudget_nonpos`
wraps this as a universal route elimination.  Thus active max-pivoting,
active-block budget control, and displayed strict-upper budget control cannot
be used as a hidden proof of the row-max defect condition exposed by the
row-max theorem surface.
The stage-budget/row-max comparison is independent too:
`not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_stageBudget_le_rowMax`
uses the same active-pivot sequence with the harmless oversized budget `3`.
All active-block and displayed off-diagonal budget hypotheses still hold, but
at displayed stage one the row maximum is `2`, so `stageBudget <= rowMax`
fails.  The row-max bridge therefore needs this comparison as a genuine
stronger invariant or visible assumption.
This makes the no-pivot red bottleneck a theorem-scope choice, not an adapter
gap: keep the remaining assumptions explicit, add a stronger
off-diagonal-control invariant, or switch to a pivoted/sorted row-wise theorem
family.  The positive QR route has now switched to the Cox--Higham
pivoted/sorted weighted least-squares family: the first local dependency,
`householderTrailingActiveVector_inner_self_ge_two_trailingNorm2Sq_of_mul_nonpos`
with signed specialization
`householderTrailingActiveVector_inner_self_ge_two_trailingNorm2Sq_signed`,
formalizes the signed Householder denominator bound
`2 ||x_tail||_2^2 <= v^T v`. The next column-pivoting dependency is also
formalized by `exists_householderTrailingColumnNorm2Sq_active_max` and
`abs_inner_householderTrailingActiveVector_column_le_vecNorm2_mul_sqrt_of_pivot_max`;
the scalar Lemma 2.1 endpoint and first row-growth step are formalized by
`abs_householderBeta_mul_inner_column_le_sqrt_two_of_signed_pivot_max` and
`abs_householder_signed_pivot_update_entry_le_one_add_sqrt_two_mul_row_bound`.
The row-sorting stage-accumulation dependency is formalized by
`scalar_growth_iterate_bound` and
`coxHigham_rowSorting_active_entry_bound_of_stage_growth`; the pivot-row
equation-(4.4) norm step is formalized by
`coxHigham_pivot_row_entry_bound_of_stage_entry_bound` with an explicit
ambient `sqrt m` factor.  Row-pivoting as an
alternative route remains available, while the scalar row-wise accumulated
perturbation dependency is now formalized by
`coxHigham_rowwise_error_accumulation_bound` and
`coxHigham_rowSorting_active_entry_bound_with_accumulated_error`.  The concrete
stored rounded panel per-step budget has also been instantiated by
`coxHigham_storedPanel_sequence_rowwise_error_accumulation_bound_of_exact_lipschitz`,
and the direct rounded row-magnitude form is
`coxHigham_storedPanel_sequence_active_entry_bound_of_exact_growth`.
The row-sorting side now has a reusable rectangular least-squares foundation:
`rectPermuteRows`, `vecPermute`, `frobNormSqRect_permuteRows`,
`rectLSGram_permuteRows`, `rectLSRhs_permuteRows`, and
`lsObjective_permuteRows` prove that applying a finite row permutation to both
the sampled/scaled matrix and right-hand side preserves the residual objective
and normal-equation data.  The column-pivoting side now has the matching
bookkeeping: `rectMatMulVec_permuteCols`, `rectLSGram_permuteCols`,
`rectLSRhs_permuteCols`, `RectLSNormalEquations.of_permuteCols`,
`lsObjective_permuteCols`, and `IsLeastSquaresMinimizer.of_permuteCols` relabel
columns and map coefficient vectors back through the inverse permutation.  The
combined wrappers `rectLSGram_permuteRowsCols`,
`rectLSRhs_permuteRowsCols`, `RectLSNormalEquations.of_permuteRowsCols`,
`lsObjective_permuteRowsCols`, and
`IsLeastSquaresMinimizer.of_permuteRowsCols` now package row sorting and column
pivoting together for the Cox--Higham handoff.  This matches the Cox--Higham
row-sorting/column-pivoting route recorded in the proof-source ledger; it is
not yet a complete pivoted/sorted QR backward-error theorem.
The next route dependency is to discharge the exact Cox--Higham growth and
sorting fields for the pivoted/sorted loop and connect that to the final
QR/preconditioner theorem.
The user-selected off-diagonal-control route is now represented by the
structure `StoredQROffDiagonalControlInvariant`.  It packages the visible local
leading-block obligations for the unpivoted stored QR solver route: nonzero
local leading determinants, local diagonal dominance, and product smallness for
the deterministic stored QR compact sequence budget times the current
pivot-column norm.  The solver-facing wrapper
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_offDiagonalControl`
proves that this single invariant supplies the existing diagonal-dominant
stored-sequence certificate and yields the repository's
`LSQRSolveBackwardError` statement with `qrSolveFinalGramBudget` and
`qrSolveFinalRhsBudget`.  This is positive progress on the chosen route, but it
does not prove that the ordinary no-pivot Householder recurrence satisfies the
invariant; that remains the next source-specific mathematical target.
The next reduction is also formalized:
`StoredQRSourceOffDiagonalControl` exposes the invariant in source-shaped
fields: local upper-triangular leading blocks, nonzero local diagonals,
row-wise off-diagonal domination, and the same stored-sequence product bound.
`StoredQROffDiagonalControlInvariant.of_sourceOffDiagonalControl` derives the
packaged invariant from these primitive fields using the existing triangular
determinant lemma, and
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl`
feeds those source-shaped hypotheses directly to the solver certificate.  The
finite-max sibling
`StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSmallness`
derives the same packaged invariant from local `IsDiagDominantUpper` leading
blocks and the canonical scalar finite-max compact-product smallness
inequality.  This narrows the packaged invariant surface while still leaving
diagonal dominance and that scalar inequality visible as source/domain
assumptions.  The
stored recurrence now also supplies the triangular shape field automatically:
`StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diag_offdiag_product`
uses the repository's prefix-lower-zero theorem, and
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diag_offdiag_product`
feeds the solver certificate from the stored recurrence plus only the nonzero
diagonal, row-wise off-diagonal domination, and compact-product smallness
obligations.  The next wrapper,
`StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_pivot_sqrtBudget_offdiag_product`,
uses the signed-alpha prefix-diagonal theorem to derive the already-written
previous diagonal entries from the stored loop and the square-root
nonbreakdown budget; its solver companion
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_pivot_sqrtBudget_offdiag_product`
keeps only the current pivot nonzero condition, the square-root
nonbreakdown budget, row-wise off-diagonal domination, and compact-product
smallness visible.  The determinant-shaped companion
`StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_sqrtBudget_offdiag_product`
and its solver wrapper
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_sqrtBudget_offdiag_product`
replace the raw current-pivot nonzero condition by nonsingularity of the
displayed local leading block, using the stored lower-zero determinant bridge.
The norm-square companion
`StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_offdiag_product`
and
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_offdiag_product`
replace the visible square-root nonbreakdown budget by the dimensioned margin
`m * B_k^2 < ||A_k(k:m,k)||_2^2`, reusing the repository's
norm-square-to-square-root Householder budget bridge.
The row-budget companion
`StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_rowBudget_product`
and
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_rowBudget_product`
decompose the remaining off-diagonal-control field into a row-growth upper
budget and a diagonal lower-bound obligation, matching the Cox--Higham
pivoted/sorted proof route.
The sharper `_rowBudget_product_of_offdiag_rows` companions record the exact
row support of that decomposition: the diagonal lower-bound comparison is
needed only for rows `i < k`, because the last row of the displayed
`(k+1) x (k+1)` leading block has no strict upper off-diagonal entry.
The named certificate `StoredQRDisplayedRowBudgetControl` now packages these
two residual row-budget obligations, and the `rowBudgetControl_product`
source-control and solver wrappers consume that package directly.  This is the
current Cox--Higham route choice made explicit: the row-growth upper bound and
matching diagonal lower-bound/nonbreakdown fact are visible source/domain data,
not hidden consequences of active-block mass or ordinary no-pivot QR.
The route-1 row-max invariant is now exposed directly by
`StoredQRDisplayedRowBudgetControl.of_rowMaxBudget_le_diag_factor`: if a
computed-loop invariant proves that each displayed strict-upper row maximum is
at most `ρ` times the corresponding displayed diagonal, with `ρ <= 1`, then
the canonical row-max budget satisfies the packaged row-budget certificate.
The source-control and solver companions
`StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_rowMaxBudgetFactor_globalProduct`
and
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_rowMaxBudgetFactor_globalProduct`
combine that contraction invariant with the stored recurrence, leading-block
nonsingularity, norm-square nonbreakdown, and the scalar finite global
compact-product budget.  This is a positive route-1 handoff, but it still does
not prove the contraction invariant from generic no-pivot Householder QR.
The scalar-defect sibling
`storedQRRowMaxDiagDefectBudget` packages the same contraction check as the
finite maximum of `rowMax - |diag|` over all displayed rows `i < k`.  The
constructor `StoredQRDisplayedRowBudgetControl.of_rowMaxDiagDefectBudget_nonpos`
and the source/solver wrappers
`StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_rowMaxDiagDefect_globalProduct`
and
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_rowMaxDiagDefect_globalProduct`
let downstream theorems use the single scalar condition
`storedQRRowMaxDiagDefectBudget <= 0`.
The stage-diagonal sibling `storedQRStageDiagLowerDefectBudget` packages the
remaining active/prefix offdiag-row diagonal lower-bound family into the single
finite scalar condition `storedQRStageDiagLowerDefectBudget <= 0`.  The theorem
`storedQRStageBudget_le_diag_of_stageDiagLowerDefectBudget_nonpos` extracts
`stageBudget k <= |(S_k)_{ii}|` for every displayed row `i < k`, and the
converse theorem
`storedQRStageDiagLowerDefectBudget_nonpos_of_stageBudget_le_diag` packages the
same pointwise family back into the scalar finite-max condition.  The
`_stageDiagDefect_offdiag_rows` source-control and solver wrappers consume that
scalar condition directly.  This is a listed dependency reduction for the
Cox--Higham route; it does not prove the scalar stage-diagonal condition from a
concrete pivoted/sorted loop.
The adapters
`storedQRStageDiagLowerDefectBudget_nonpos_of_rowMaxDiagDefectBudget_nonpos_stageBudget_le_rowMax`
and
`storedQRStageDiagLowerDefectBudget_nonpos_of_diagDominant_stageBudget_le_rowMax`
connect this scalar condition to the row-max branch: if the uniform stage budget
is bounded by each displayed row maximum, then nonpositive row-max defect, or
local diagonal dominance, implies nonpositive stage-diagonal defect.
The comparison package `storedQRStageRowMaxComparisonDefectBudget` now carries
that remaining `stageBudget <= rowMax` family as a single finite maximum:
`storedQRStageBudget_le_rowMax_of_stageRowMaxComparisonDefectBudget_nonpos`
extracts the displayed comparison, the converse theorem packages a pointwise
comparison proof back into scalar nonpositivity, and the scalar bridge
`storedQRStageDiagLowerDefectBudget_nonpos_of_rowMaxDiagDefectBudget_nonpos_stageRowMaxComparisonDefectBudget_nonpos`
feeds the stage-diagonal condition from the two scalar row-max assumptions.
The scalar-comparison wrappers
`..._activeMaxPivot_completedColumns_globalProduct_rowMaxDiagDefect_stageRowMaxComparisonDefect_offdiag_rows`
and their solver-facing and actual-unit-roundoff siblings now thread this
two-scalar surface through the active-pivot source-control and local
backward-error theorems.  The local QR handoff therefore no longer needs the
stage-budget/row-max comparison as a displayed family, although the row-max
defect and comparison defect themselves are still visible assumptions.
The diagonal-dominant scalar-comparison siblings
`StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_stageRowMaxComparisonDefect_offdiag_rows`
and
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_stageRowMaxComparisonDefect_offdiag_rows`
go one step further on the local source-control/solver surface: local
diagonal dominance now supplies the leading-block determinant field and, with
the scalar comparison defect, supplies
`storedQRStageDiagLowerDefectBudget <= 0`.  The comparison scalar,
conditioning and dual compact-budget data, active-pivot policy, compact-product
smallness, and final generic QR/preconditioner theorem remain visible.
Their finite-max siblings
`StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSmallness_stageRowMaxComparisonDefect_offdiag_rows`
and
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSmallness_stageRowMaxComparisonDefect_offdiag_rows`
derive the raw compact-product field from the canonical finite-max scalar
involving `storedQRDiagDominantInvFactorBudget`,
`storedQRCompactSequenceRelativeBudget`, and
`storedQRPivotColumnNormBudget`.
The active source-denominator rational-gamma siblings
`StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows`
and
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows`
replace that assembled finite-max scalar on the local source-control and
solver surface by raw source-denominator nonbreakdown, `fp.u <= Ucap`,
`(m : Real) * Ucap < 1`, and the canonical rational-gamma cap smallness
inequality.  Local diagonal dominance, the scalar comparison defect,
active-pivot policy, signed-stage recurrence budgets, source-denominator and
unit-roundoff cap obligations, and the final generic QR/preconditioner theorem
remain visible.
The horizon-clamped source-denominator sibling
`StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows_of_horizonBudget`
uses `storedQRStageRowMaxComparisonDefectBudget_nonpos_of_horizonBudget` and
`qrStageHorizonBudget` to derive the old global monotonicity field from the
signed-stage compact recurrence.  It removes only global budget monotonicity
from this local source-control surface; diagonal dominance, active pivoting,
the scalar comparison defect, denominator/cap smallness, and the final QR
theorem remain visible.
The actual-unit stored-lower siblings
`storedQRSourceDenominator_ne_zero_of_diagDominant_signedAlphaDef_stored_trailing_sequence`,
`StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_storedLower_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows_of_actualUnitRoundoff_no_gammaValid`,
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_storedLower_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows_of_actualUnitRoundoff_no_gammaValid`, and
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver_of_actualUnitRoundoff_no_gammaValid`
derive the raw source-denominator nonbreakdown field from the stored recurrence,
the signed-alpha definition, and local diagonal dominance.  The active actual-
unit branch therefore keeps scalar smallness, local diagonal dominance,
comparison, active-pivot, and signed-stage budget obligations visible, but no
longer exposes the raw denominator proof.
The route-elimination theorem
`not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_stageBudget_le_rowMax`
shows that the needed `stageBudget <= rowMax` comparison is not a consequence
of the current active max-pivot plus active/off-diagonal budget hypotheses
alone.
The scalar wrappers
`not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`
and
`not_forall_leadingBlock_upper_det_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`
lift this failed route to the finite comparison defect itself: active-pivot
budget data, even with product compact-smallness added, cannot make
`storedQRStageRowMaxComparisonDefectBudget <= 0` automatic.
The row-max-granted route eliminations
`not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_rowMaxDiagDefect_implies_stageRowMaxComparisonDefectBudget_nonpos`
and
`not_forall_leadingBlock_upper_det_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_rowMaxDiagDefect_implies_stageRowMaxComparisonDefectBudget_nonpos`
go one step further: the witness
`activeMaxPivotRowMaxComparisonCounterexample_stageRowMaxComparisonDefectBudget_pos`
has nonpositive row-max scalar defect but positive comparison scalar defect.
Thus even granting `storedQRRowMaxDiagDefectBudget <= 0`, and even adding the
compact-product hypotheses, does not make the comparison defect automatic.
The row-max-alone scalar-stage route is also ruled out by
`not_forall_rowMaxDiagDefectBudget_implies_stageDiagLowerDefectBudget_nonpos`:
the same diagonally safe witness with uniform stage budget `4` has positive
`storedQRStageDiagLowerDefectBudget`.  Thus the row-max bridge genuinely needs
the separate comparison scalar or an equivalent stronger loop invariant.
The product/active row-max-granted scalar-stage route is ruled out as well:
`not_forall_leadingBlock_upper_det_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_rowMaxDiagDefect_implies_stageDiagLowerDefectBudget_nonpos`
uses the same witness with compact budget `B = 1/16`, active max-pivoting,
active/off-diagonal budget control, and nonpositive row-max scalar defect, but
still obtains positive `storedQRStageDiagLowerDefectBudget`.  The companion
`not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_rowMaxDiagDefect_implies_stageDiagLowerDefectBudget_nonpos`
derives the active-only obstruction from the product-strengthened one.
The scalar-stage counterpart
`not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_stageDiagLowerDefectBudget_nonpos`
shows that the same active-pivot budget surface alone also cannot imply the
nonpositive `storedQRStageDiagLowerDefectBudget` condition.
The companion route-elimination theorem
`not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_rowMaxDiagDefectBudget_nonpos`
shows that the nonpositive row-max scalar defect itself is not a consequence of
the same active-pivot/budget surface either: the active-pivot witness has
strict-upper row maximum `2` and displayed diagonal magnitude `1` at stage one.
The product-smallness cross-route obstruction
`not_forall_upper_tri_det_ne_zero_product_budget_implies_rowMaxDiagDefectBudget_nonpos`
also rules out deriving this row-max defect condition merely from triangular
nonsingularity plus a satisfiable compact-product inequality.
The stronger active-budget/product obstruction
`not_forall_leadingBlock_upper_det_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_rowMaxDiagDefectBudget_nonpos`
uses the same active-pivot sequence and `B = 1/16` to show that active
max-pivoting and active/off-diagonal budget control do not rescue the
row-max scalar defect route.
The companion scalar-stage obstruction
`not_forall_upper_tri_det_ne_zero_product_budget_implies_stageDiagLowerDefectBudget_nonpos`
uses the same witness with constant stage budget `2`, so product smallness
cannot supply the finite stage-diagonal lower-bound condition either.
The stronger active-budget/product scalar-stage obstruction
`not_forall_leadingBlock_upper_det_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_stageDiagLowerDefectBudget_nonpos`
shows that the active-pivot sequence satisfies the active budget and
product-smallness hypotheses while the constant-budget scalar stage-diagonal
defect remains positive.
Even product smallness added to the active-pivot budget surface does not rescue
the comparison:
`not_forall_leadingBlock_upper_det_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_stageBudget_le_rowMax`
uses the same active-pivot sequence with stage budget `3`, while the row
maximum at displayed stage one is still `2`.
The actual-unit-roundoff sibling
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_rowMaxDiagDefect_globalProduct_of_actualUnitRoundoff_no_gammaValid`
derives the local `gammaValid fp m`/`gammaValid fp n` guards from the displayed
scalar condition `(m : ℝ) * fp.u < 1`, while keeping the determinant,
norm-square nonbreakdown, row-defect, and global product assumptions visible.
The bridge `storedQRRowMaxDiagDefectBudget_nonpos_of_diagDominant` proves that
local `IsDiagDominantUpper` displayed leading blocks imply this scalar defect
condition, and `StoredQRDisplayedRowBudgetControl.of_diagDominant` turns that
directly into the packaged row-budget certificate.  This reuses diagonal
dominance when it is supplied; it still does not prove diagonal dominance from
generic no-pivot Householder QR.
The route-elimination pair
`exactHouseholderQRDiagDominanceCounterexample_rowMaxDiagDefectBudget_pos` and
`not_forall_exact_trailing_householder_sequence_implies_rowMaxDiagDefectBudget_nonpos`
shows that exact no-pivot trailing Householder recurrence, valid squared-norm
identities, and nonzero denominators do not imply this scalar condition.
The stage-diagonal route has the analogous obstruction:
`exactHouseholderQRDiagDominanceCounterexample_stageDiagLowerDefectBudget_pos`
and
`not_forall_exact_trailing_householder_sequence_implies_stageDiagLowerDefectBudget_nonpos`
show that even for the constant stage budget `2`, the exact no-pivot
recurrence alone cannot prove `storedQRStageDiagLowerDefectBudget <= 0`.
The comparison scalar has the same exact-recurrence obstruction:
`exactHouseholderQRDiagDominanceCounterexample_stageRowMaxComparisonDefectBudget_pos`
and
`not_forall_exact_trailing_householder_sequence_implies_stageRowMaxComparisonDefectBudget_nonpos`
show that exact no-pivot recurrence, signed squared-norm identities, nonzero
denominators, and nonnegative stage budgets still do not imply
`storedQRStageRowMaxComparisonDefectBudget <= 0`.
The stored-panel actual-unit strengthening lifts both scalar obstructions to
the current source surface:
`not_forall_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_implies_stageDiagLowerDefectBudget_nonpos`
and
`not_forall_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`
use the exact FP model with `fp.u = 0`, the stored recurrence, signed-alpha
equation, nonzero source denominators, and `(2 : ℝ) * fp.u < 1`; the constant
stage budgets `2` and `3` still make the scalar stage-diagonal and comparison
defects positive.
The diagonal-dominant stored-surface strengthening uses the exact stored
sequence from `[[3,2],[0,1]]`:
`storedDiagDominantComparisonCounterexample_stored_step`,
`storedDiagDominantComparisonCounterexample_rhs_step`,
`storedDiagDominantComparisonCounterexample_diagDominant`,
`storedDiagDominantComparisonCounterexample_activeMaxPivotChoice`,
`storedDiagDominantComparisonCounterexample_compactSequenceProductBudget_lt_one`,
`storedDiagDominantComparisonCounterexample_finiteMaxSmallness`,
`not_forall_diagDominant_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageDiagLowerDefectBudget_nonpos`,
and
`not_forall_diagDominant_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`
show that even adding local diagonal dominance to stored recurrence,
signed-alpha, source-denominator, actual-unit validity, and nonnegative stage
budgets does not force the scalar diagonal-lower or stage-budget/row-max
comparison defects.  The active-pivot strengthening
`not_forall_diagDominant_activeMaxPivot_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`
shows the comparison scalar is still not forced after adding the finite active
max-pivot selector policy.  The compact-product strengthening
`not_forall_diagDominant_activeMaxPivot_product_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`
adds the stored RHS recurrence and exact/zero-RHS compact-product smallness;
the same scalar comparison defect remains positive.  The finite-max
strengthening
`not_forall_diagDominant_activeMaxPivot_finiteMaxSmallness_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`
uses the canonical finite-max compact-product scalar itself, which is also
zero-small for this exact/zero-RHS witness, and still leaves the comparison
defect positive.
The signed-stage global-budget strengthening
`storedDiagDominantComparisonCounterexample_globalCompactBudget_recurrence` and
`not_forall_diagDominant_activeMaxPivot_globalCompactBudget_finiteMaxSmallness_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`
uses a nonconstant nonnegative stage budget `0, 3, 10, ...`: the exact
finite global compact-update budgets are zero and the Cox--Higham factor in
dimension two is bounded by `3`, so the global compact-step recurrence holds;
nevertheless the stage-one scalar comparison defect remains positive.  Thus
even granting the signed-stage recurrence budget does not make the comparison
invariant automatic.
The row-max-granted signed-stage strengthening
`storedDiagDominantComparisonCounterexample_rowMaxDiagDefectBudget_nonpos` and
`not_forall_diagDominant_activeMaxPivot_globalCompactBudget_finiteMaxSmallness_rowMaxDiagDefect_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`
uses the same witness and proves its finite row-max/diagonal defect scalar is
nonpositive.  Consequently even row-max defect control, diagonal dominance,
active pivoting, signed global-budget recurrence, canonical finite-max
compact-product smallness, stored recurrence, actual-unit facts, and
nonnegative stage budgets do not force the comparison scalar.
The determinant-strengthened signed-stage route
`storedDiagDominantComparisonCounterexample_leadingBlock_det_ne_zero` and
`not_forall_diagDominant_activeMaxPivot_leadingBlock_det_ne_zero_globalCompactBudget_finiteMaxSmallness_rowMaxDiagDefect_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`
adds nonsingular displayed leading blocks to that same witness: the stage-zero
block has determinant `3`, the stage-one block has determinant `-3`, and the
stage-one scalar comparison defect is still positive.
The conditioning-strengthened signed-stage route adds
`storedDiagDominantComparisonCounterexampleKappaBudget`,
`storedDiagDominantComparisonCounterexampleKappaNormSqBudget`,
`storedDiagDominantComparisonCounterexample_kappaBudget_le`,
`storedDiagDominantComparisonCounterexample_kappaNormSqBudget`,
`storedDiagDominantComparisonCounterexample_dualBudget`, and
`not_forall_diagDominant_activeMaxPivot_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_globalCompactBudget_finiteMaxSmallness_rowMaxDiagDefect_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`.
The exact compact-component budget is zero, so the local `kappaInf`/self-norm
and dual compact-budget fields also coexist with the positive scalar comparison
defect.
The final-surface comparison route
`storedDiagDominantComparisonCounterexampleFinalSurfaceStageBudget`,
`storedDiagDominantComparisonCounterexample_finalSurfaceStageBudget_nonneg`,
`storedDiagDominantComparisonCounterexample_finalSurfaceStageBudget_mono`,
`storedDiagDominantComparisonCounterexample_finalSurface_init`,
`storedDiagDominantComparisonCounterexample_finalSurface_initBlock`,
`storedDiagDominantComparisonCounterexample_finalSurface_globalCompactBudget_recurrence`,
`storedDiagDominantComparisonCounterexample_stageRowMaxComparisonDefectBudget_pos_finalSurfaceStageBudget`,
and
`not_forall_diagDominant_activeMaxPivot_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_init_globalProduct_globalCompactBudget_rowMaxDiagDefect_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonneg_monoStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`
uses the budget `3, 10, 30, ...`: the initial full-block and displayed
row-budget fields, global compact-product smallness, signed-stage global
compact-budget recurrence, nonnegative monotone budget, determinant,
conditioning/dual budget, row-max defect, active-pivot, and diagonal-dominance
facts all hold for the same exact witness, but the stage-one scalar
stage-budget/row-max comparison defect is still positive.
The source-denominator final-surface refinement
`storedDiagDominantComparisonCounterexample_finalSurface_sourceDenURationalGammaCanonicalSmallness`
and
`not_forall_diagDominant_activeMaxPivot_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_init_sourceDenURationalGammaCanonical_globalCompactBudget_rowMaxDiagDefect_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonneg_monoStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`
sets `Ucap = 0` on the same exact witness, so the canonical rational-gamma
finite-max scalar holds while the comparison defect remains positive.
`StoredQRDisplayedRowBudgetControl.of_signed_stage_budgets_factor_of_normSqBudget`
builds this named certificate from the existing signed-stage Cox--Higham
row-growth theorem, deriving the pivot-column zeroing field from the same
norm-square nonbreakdown budget and keeping only the diagonal lower-bound field
visible.
`StoredQRDisplayedRowBudgetControl.of_signed_stage_uniformBudget_factor_of_normSqBudget`
specializes that package to a single monotone stage-budget sequence, using
`qrLeadingOffdiagStop_le` to remove the separate terminal row-budget-domination
field while keeping the offdiag-row diagonal lower-bound/nonbreakdown
obligation explicit.
The same correction is propagated through the stage-budget, signed-stage,
norm-square-derived pivot-zeroing, uniform-stage, and concrete
stage-entry-bound handoffs.  Thus later Cox--Higham QR certificates no longer
silently reintroduce a diagonal lower-bound condition for the non-offdiagonal
row `i = k`.
The QR-side row-growth bridge
`fl_householderStoredPanel_sequence_leadingBlock_offdiag_budget_of_exact_stage_budgets_factor`
now converts Cox--Higham stage budgets into the displayed leading-block
off-diagonal upper field used by that decomposition.  It uses
`qrLeadingOffdiagStop` to distinguish the current displayed column from a
completed column and
`fl_householderStoredPanel_sequence_completed_column_eq_pivot_succ` to reuse
the value written when a completed column left the active panel.  This closes
the row-growth propagation half only; the matching diagonal lower-bound
obligation is still visible.
The signed-stage companion
`fl_householderStoredPanel_sequence_leadingBlock_offdiag_budget_of_signed_stage_budgets_factor`
specializes that bridge to the actual signed trailing Householder stages
`storedQRSignedStageVector` and `storedQRSignedStageBeta`, removing the generic
reflector-family parameter from the row-growth dependency.  The concrete
stage-budget, exact same-reflector, pivot-zeroing, and terminal domination
fields remain visible.
The local exact same-reflector split
`storedQRSignedStage_exact_same_reflector_bound_of_prefix_or_active_stage_bounds`
now handles one signed stored-QR stage without an opaque row case split:
prefix rows are preserved by the zero-prefix Householder identity, while active
rows reuse the Cox--Higham signed-pivot row-growth theorem.  It still keeps
pivot maximality, positive trailing norm, and stage entry bounds visible.
The exact pivot-column zeroing field is now supplied by
`storedQRSignedStage_pivot_column_zero_below_of_trailingNorm_pos` and
`storedQRSignedStage_pivot_zeroing_field_of_trailingNorm_pos`: under the
signed-alpha convention and positive trailing-norm nonbreakdown, exact
application of the signed trailing Householder reflector zeros the active pivot
column below the pivot.  The remaining Cox--Higham obligations are the stage
recurrence/exact same-reflector bounds, terminal row-budget domination,
diagonal lower bounds, and compact-product smallness.
The companion `storedQRSignedStage_pivot_zeroing_field_of_normSqBudget` derives
that pivot-zeroing field from the norm-square nonbreakdown budget already used
by the source-control route, so downstream least-squares handoffs no longer
need an independent `hpivot` hypothesis.
The solver-facing stage-budget companion
`StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_stageBudget_rowBudget_product`
and
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_stageBudget_rowBudget_product`
compose that QR-side row-growth bridge with the row-budget decomposition, so
the local QR solve certificate can now consume Cox--Higham stage budgets plus
explicit diagonal lower bounds directly.
The signed-stage solver-facing variants
`StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageBudget_rowBudget_product`
and
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageBudget_rowBudget_product`
instantiate those handoffs with `storedQRSignedStageVector` and
`storedQRSignedStageBeta`, so later Cox--Higham work no longer has to carry an
arbitrary reflector sequence through the least-squares layer.
The `_of_normSqBudget` signed-stage variants additionally compose the derived
pivot-zeroing adapter, leaving only the stage recurrence, exact same-reflector
bounds, row-budget diagonal lower bounds, determinant/norm-square
nonbreakdown, and compact-product assumptions visible.
The uniform-stage-budget variants use `qrLeadingOffdiagStop_le` and monotonicity
of one Cox--Higham budget sequence to remove the separate terminal
row-budget-domination field; the remaining diagonal lower bound is the explicit
condition `stageBudget k <= |(S_k)_{ii}|`.
The `_stage_entry_bounds` uniform variants additionally consume
`storedQRSignedStage_exact_same_reflector_bound_of_prefix_or_active_stage_bounds`
directly, so the abstract exact-reflector `hexact` field is now derived from
concrete stage row/column entry bounds, pivot maximality, and norm-square
nonbreakdown.  This still leaves the diagonal lower-bound and compact-product
fields visible.
The active/prefix stage-entry companions
`StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_stage_entry_bounds_offdiag_rows`
and
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_stage_entry_bounds_offdiag_rows`
make the remaining entry-control fields more source-shaped: one active-suffix
block bound supplies all active row/column estimates, and only prefix displayed
rows keep a separate row-bound hypothesis.
The active-block-recurrence variants
`StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_offdiag_rows`
and
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_offdiag_rows`
derive that active-suffix block bound from the local Cox--Higham signed-pivot
active-block recurrence.  The visible stage-entry burden is therefore narrowed to
the initial active-block budget, the active-block budget recurrence, completed
old-column preservation, and the separate prefix displayed-row budget.
The prefix-row-recurrence variants
`storedQRSignedStage_active_block_bound_of_signed_stage_budget`,
`storedQRSignedStage_prefix_row_bound_of_active_block_and_prefix_budget`,
`StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_prefixRowRecurrence_offdiag_rows`,
and
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_prefixRowRecurrence_offdiag_rows`
factor the active-block theorem into a reusable bound and derive the prefix
displayed-row stage bound from a one-step prefix budget.  This removes the raw
prefix-row-bound hypothesis from the QR handoff.  The global compact-budget
variants
`storedQRSignedStage_completed_column_preservation`,
`storedQRSignedStageGlobalCompactBudget`,
`storedQRSignedStageGlobalCompactBudget_nonneg`,
`storedQRSignedStage_active_prefix_budgets_of_globalCompactBudget`,
`storedQRSignedStageBudget_mono_on_stages_of_globalCompactBudget`,
`StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_globalCompactBudget_offdiag_rows`,
and
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_globalCompactBudget_offdiag_rows`
replace the separate off-diagonal, active-block, and prefix-row one-step
budget fields by a single finite maximum compact-update budget at each stage;
the same recurrence now also proves that nonnegative stage budgets are monotone
on the QR stage horizon `b <= n`.  The horizon-clamped budget helper
`qrStageHorizonBudget` and the completed-column global-product
`_offdiag_rows_of_horizonBudget` source-control/solver wrappers reuse older
global-monotone theorem surfaces while preserving this stage-range-only
interpretation.
The completed-column variants
`StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_globalCompactBudget_completedColumns_offdiag_rows`
and
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_globalCompactBudget_completedColumns_offdiag_rows`
also derive old-column preservation from the stored QR lower-zero invariant and
the zero-prefix Householder support lemma.  The global-product variants
`storedQRCompactSequenceProductBudget`,
`storedQRCompactSequenceProductExpr_le_budget`,
`storedQRCompactSequenceProductBudget_lt_one_of_forall_expr_lt`,
`storedQRCompactSequenceProductBudget_lt_one_of_forall_pivot_product`,
`storedQRCompactSequenceProductBudget_lt_one_of_relativeBudget_eq_zero`,
`storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_factor_norm_bounds`,
`storedQRDiagDominantInvFactorBudget`,
`storedQRDiagDominantInvFactor_le_budget`,
`storedQRDiagDominantInvFactorBudget_nonneg`,
`storedQRPivotColumnNormBudget`,
`storedQRPivotColumnNorm_le_budget`,
`storedQRPivotColumnNormBudget_nonneg`,
`storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_smallness`,
`storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_relativeBudget_le`,
`storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_stepBudget_le`,
`storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_columnRhsBudget_le`,
`StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSmallness`,
`StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_diagDominant_finiteMaxSmallness`,
`StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_diagDominant_finiteMaxSmallness`,
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_diagDominant_finiteMaxSmallness`,
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_diagDominant_finiteMaxSmallness_concreteDual`,
`storedQRSignedStage_normSqBudget_of_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget`,
`StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_globalCompactBudget_completedColumns_globalProduct_offdiag_rows`,
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_globalCompactBudget_completedColumns_globalProduct_offdiag_rows`,
`StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_completedColumns_globalProduct_offdiag_rows`,
and
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_completedColumns_globalProduct_offdiag_rows`
replace all per-pivot compact-product hypotheses by one finite maximum
condition `storedQRCompactSequenceProductBudget < 1`.  The stage-diagonal-defect
siblings
`StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_globalCompactBudget_completedColumns_globalProduct_stageDiagDefect_offdiag_rows`,
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_globalCompactBudget_completedColumns_globalProduct_stageDiagDefect_offdiag_rows`,
`StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_completedColumns_globalProduct_stageDiagDefect_offdiag_rows`,
and
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_completedColumns_globalProduct_stageDiagDefect_offdiag_rows`
also replace the offdiag-row diagonal lower-bound family by
`storedQRStageDiagLowerDefectBudget <= 0`.  The converse finite-maximum adapter
proves that the global condition follows whenever every per-pivot product
expression is already below `1`.  The zero-budget adapter records the
exact/zero-compact special case: if the stored compact relative budget is
exactly `0`, then the global compact-product condition is automatic.  It does
not prove floating-point smallness when the compact relative budget is
positive.  The scalar adapter
`storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_factor_norm_bounds`
reduces this product-smallness obligation to global bounds on the
diagonal-dominant inverse-budget factors and displayed pivot-column norms plus
one scalar inequality.  The finite-max adapter supplies those two global bounds
canonically from finite maxima, leaving only the scalar inequality for the
canonical budgets.  The relative-budget-cap adapter records the corresponding
positive-budget threshold: if the compact relative budget is bounded by a
nonnegative scalar `cmax`, then it is enough to check the same canonical scalar
product condition with `cmax`.  This still leaves the cap and the scalar
inequality as visible numerical obligations.  The per-step cap adapter
`storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_stepBudget_le`
specializes this threshold with `cmax = n * cStep` whenever every stored QR
compact panel step has relative budget at most `cStep`; it still leaves the
uniform per-step cap and the scalar inequality as visible obligations.  The
column/RHS cap adapter
`storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_columnRhsBudget_le`
uses `householderCompactPanelRelativeBudget_le_mul_add_of_column_rhs_le` and
`storedQRCompactStepRelativeBudget_le_mul_add_of_column_rhs_le` to replace that
uniform step cap by vector-level caps `cCol` and `cRhs`, with sequence cap
`n * (n * cCol + cRhs)`.  Its norm-budget companion
`storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_columnRhsNormBudget_le`
uses `householderCompactRelativeBudget_le_of_normBudget_le_mul`,
`householderCompactPanelRelativeBudget_le_mul_add_of_normBudget_le_mul`, and
`storedQRCompactStepRelativeBudget_le_mul_add_of_normBudget_le_mul` to replace
those already-normalized relative caps by primitive norm-budget inequalities.
The componentwise companion
`storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_columnRhsComponentBudget_le`
uses `householderCompactNormBudget_le_mul_of_componentBudget_le_mul_abs`,
`householderCompactPanelRelativeBudget_le_mul_add_of_componentBudget_le_mul_abs`,
and
`storedQRCompactStepRelativeBudget_le_mul_add_of_componentBudget_le_mul_abs` to
start from entrywise compact-budget inequalities.  The newer norm-coefficient
route `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_normBudgetCoeff_le`
uses `householderAbsDotBudget_le_vecNorm2_mul`,
`householderCompactComponentBudget_le_updateCoeff_mul_norm`,
`householderCompactNormBudget_le_normBudgetCoeff_mul`, and
`storedQRCompactStepRelativeBudget_le_mul_add_normBudgetCoeff` to avoid the
fragile entrywise-relative requirement: the compact update is charged against
`||input||_2 |v_i|`, while only the final subtraction is charged against
`|input_i|`.  Its finite-max sibling
`storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_normBudgetCoeffBudget`
chooses the maximum stage coefficient inside Lean, leaving local diagonal
dominance and the scalar smallness condition in terms of that canonical
displayed budget as visible obligations.  The bounded scalar certificates
`storedQRCompactNormBudgetCoeffSmallness_of_bounds`,
`storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_normBudgetCoeffBudget_bounds`,
and
`StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxNormBudgetCoeffBoundedSmallness`
let this condition be checked using displayed upper bounds `Dmax`, `Cmax`, and
`Nmax` for the diagonal-dominant inverse factor, coefficient maximum, and
pivot-column norm budget.  The pointwise-bound siblings
`storedQRDiagDominantInvFactorBudget_le_of_forall_le`,
`storedQRPivotColumnNormBudget_le_of_forall_le`,
`storedQRCompactStepNormBudgetCoeffBudget_le_of_forall_le`,
`storedQRCompactNormBudgetCoeffSmallness_of_pointwise_bounds`,
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_normBudgetCoeffBudget_pointwise_bounds`,
  and
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxNormBudgetCoeffPointwiseBounds`
  show that those displayed upper-bound hypotheses follow from per-pivot route
  estimates, plus nonnegativity of `Dmax`, `Cmax`, and `Nmax` for the zero-pivot
  edge case.  The coefficient-estimate branch
  `householderCompactNormBudgetCoeff_eq_u_add_abs_beta_norm_sq_mul_factor`,
  `householderCompactNormBudgetCoeff_le_of_abs_beta_norm_sq_le`,
  `storedQRCompactStepNormBudgetCoeff_le_of_forall_abs_beta_norm_sq_le`,
  `storedQRCompactStepNormBudgetCoeffBudget_le_of_forall_abs_beta_norm_sq_le`,
  `storedQRCompactNormBudgetCoeffSmallness_of_pointwise_absBetaNormSq_bounds`,
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_absBetaNormSqPointwiseBounds`,
  and
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxAbsBetaNormSqPointwiseBounds`
  specializes `Cmax` to the explicit scalar
  `u + Bmax * householderCompactNormBudgetCoeffFactor fp m` when every signed
  stage satisfies `|beta_k| * ||v_k||_2^2 <= Bmax`.  This reduces the open
  coefficient pointwise estimate to the standard Householder normalization.
  The exact-normalization siblings
  `abs_householderBeta_mul_vecNorm2_sq_eq_two`,
  `storedQRSignedStage_abs_beta_norm_sq_eq_two_of_den_ne_zero`,
  `storedQRCompactStepNormBudgetCoeff_le_of_forall_source_den_ne_zero`,
  `storedQRCompactStepNormBudgetCoeffBudget_le_of_forall_source_den_ne_zero`,
  `storedQRCompactNormBudgetCoeffSmallness_of_pointwise_source_den_ne_zero_bounds`,
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_sourceDenPointwiseBounds`,
  and
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSourceDenPointwiseBounds`
  close that beta-normalization branch with the concrete value `Bmax = 2`
  whenever the signed-stage Householder denominators are nonzero.  The
  source-facing scalar-smallness siblings
  `storedQRCompactNormBudgetCoeffSmallness_of_pointwise_source_den_ne_zero_simple_bounds`,
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_sourceDenSimpleBounds`,
  and
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSourceDenSimpleBounds`
  rewrite the remaining scalar condition as
  `2 * Dmax * (m * ((n * (n + 1) * (u + 2F_m) * Nmax)^2)) < 1`.
  The cap siblings
  `storedQRCompactNormBudgetCoeffSmallness_of_pointwise_source_den_ne_zero_cap_bounds`,
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_sourceDenCapBounds`,
  and
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSourceDenCapBounds`
  further show that this scalar condition follows from upper caps
  `u <= Ucap` and `F_m <= Fcap` and the displayed inequality with
  `Ucap + 2Fcap`.
  The Householder-side cap theorem
  `householderCompactNormBudgetCoeffFactor_le_of_u_gamma_le` bounds
  `F_m = householderCompactNormBudgetCoeffFactor fp m` by the explicit
  polynomial in caps `Ucap` and `Gcap` whenever `fp.u <= Ucap` and
  `gamma fp m <= Gcap`.
  The shared rounding lemmas `gammaValid_of_u_le_cap`,
  `gamma_le_of_u_le_cap`, and
  `gamma_le_Gcap_of_u_le_cap` supply the matching gamma cap from a
  unit-roundoff cap and the displayed rational bound
  `(m * Ucap) / (1 - m * Ucap) <= Gcap`.
  The composed Householder theorem
  `householderCompactNormBudgetCoeffFactor_le_of_u_cap_gamma_cap` packages
  these two steps, so the coefficient-factor cap can be derived directly from
  `fp.u <= Ucap`, `(m : Real) * Ucap < 1`, and the displayed rational
  domination by `Gcap`.
  The least-squares wrappers
  `storedQRCompactNormBudgetCoeffSmallness_of_pointwise_source_den_ne_zero_uGammaCapBounds`,
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_sourceDenUGammaCapBounds`,
  and
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSourceDenUGammaCapBounds`
  compose that displayed factor cap into the source-denominator scalar
  smallness, compact-product, and off-diagonal-control invariant surfaces.
  The rational-gamma siblings
  `storedQRCompactNormBudgetCoeffSmallness_of_pointwise_source_den_ne_zero_uRationalGammaCapBounds`,
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_sourceDenURationalGammaCapBounds`,
  and
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSourceDenURationalGammaCapBounds`
  specialize `Gcap` to `(m * Ucap)/(1 - m * Ucap)`, so the route no longer
  carries a separate rational-domination proof field.
  The canonical finite-max siblings
  `storedQRCompactNormBudgetCoeffSmallness_of_source_den_ne_zero_uRationalGammaCanonicalBounds`,
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_sourceDenURationalGammaCanonicalBounds`,
  and
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSourceDenURationalGammaCanonicalBounds`
  further choose the displayed `Dcap` and `Ncap` as the repository's canonical
  finite maxima, removing the separate pointwise inverse-factor and
  pivot-column domination proof fields from this rational-gamma surface.
  The solver-facing and probability-level siblings
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_finiteMaxSourceDenURationalGammaCanonicalBounds`
  and
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSourceDenURationalGammaCanonicalBounds_solver`
  compose that canonical source-denominator cap route into the equation (8)
  stored-QR solve certificate and the high-probability rounded sampled-row
  objective theorem.
  The active scalar-comparison local siblings
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows`
  use the same canonical source-denominator rational-gamma cap route for the
  active-pivot diagonal-dominant scalar-comparison branch, so this local branch
  no longer exposes the assembled finite-max scalar involving
  `storedQRCompactSequenceRelativeBudget`.
  The model-level route-elimination theorem `FPModel.not_forall_u_le_cap`,
  using `FPModel.exactWithUnitRoundoff`, proves that no fixed numerical
  `Ucap` can be derived from the abstract `FPModel` alone; the primitive cap
  `fp.u <= Ucap` must therefore remain a visible floating-point/domain
  assumption unless a more concrete machine model is introduced.
  The canonical scalar route-elimination theorem
  `not_forall_diagDominant_sourceDen_uCap_implies_uRationalGammaCanonicalSmallness`
  similarly shows that the displayed canonical finite-max scalar smallness
  condition is not forced by diagonal dominance, source nonbreakdown,
  `fp.u <= Ucap`, and `m * Ucap < 1`, even in a `1 x 1`
  exact-with-unit-roundoff witness.
  The companion
  `not_forall_diagDominant_sourceDen_actualU_implies_uRationalGammaCanonicalSmallness`
  removes the cap notation entirely and plugs the actual `fp.u` into the same
  rational-gamma expression; the same kind of witness still falsifies the
  scalar inequality.  The signed-alpha strengthening
  `not_forall_diagDominant_signedAlphaDef_sourceDen_actualU_implies_uRationalGammaCanonicalSmallness`
  and its no-`gammaValid` sibling
  `not_forall_diagDominant_signedAlphaDef_sourceDen_actualU_no_gammaValid_implies_uRationalGammaCanonicalSmallness`
  show the same obstruction after exposing the concrete signed Householder
  scalar rule and replacing operation validity by `(m : Real) * fp.u < 1`.
  The stored-recurrence strengthening
  `not_forall_diagDominant_signedAlphaDef_stored_trailing_sequence_actualU_no_gammaValid_implies_uRationalGammaCanonicalSmallness`
  shows the obstruction persists even after the actual stored panel recurrence
  replaces the raw denominator field on the stored-lower branch.
  Thus this branch needs an independent scale/conditioning smallness theorem,
  not merely a cleaner choice of unit-roundoff parameter.
  The source nonbreakdown handoff
  `storedQRSourceDenominator_ne_zero_of_trailingNorm2Sq_pos_mul_nonpos`,
  together with the canonical invariant, solver, and probability wrappers
  carrying `trailingNormPos` in their names, removes raw Householder
  denominator nonbreakdown from this branch by deriving it from the signed-alpha
  source facts `alpha_k^2 = ||A_k(k:m,k)||_2^2`,
  `||A_k(k:m,k)||_2^2 > 0`, and `alpha_k A_k(k,k) <= 0`.
  The determinant-facing siblings
  `StoredQROffDiagonalControlInvariant.of_diagDominant_leadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds`,
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_leadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds`,
  and
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_leadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds_solver`
  further derive those positive trailing norms from nonzero previous/current
  leading-block determinants plus the stored lower-zero shape.
  The invariant-level sibling
  `StoredQROffDiagonalControlInvariant.of_diagDominant_signedAlphaDef_leadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds`
  also derives the squared-alpha and sign-choice scalar fields directly from
  the concrete `signedHouseholderAlpha` definition, so this determinant-facing
  invariant route no longer exposes those two algebraic facts separately.
  The determinant-facing solver theorem now feeds this packaged invariant into
  the generic off-diagonal-control solver handoff, so the theorem is used in the
  solver path rather than merely recorded as a standalone adapter.
  The current-determinant siblings
  `StoredQROffDiagonalControlInvariant.of_diagDominant_signedAlphaDef_previousLeadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds`,
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_previousLeadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds`, and
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_previousLeadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds_solver`
  remove the current leading-block determinant hypothesis by deriving it from
  `IsDiagDominantUpper`; only the previous transposed leading-block determinant
  remains visible on this branch.  The lower-previous-shape siblings
  `qrPreviousLeadingBlockTranspose_det_ne_zero_of_diagDominant_leadingBlock`,
  `StoredQROffDiagonalControlInvariant.of_diagDominant_signedAlphaDef_lowerPrev_finiteMaxSourceDenURationalGammaCanonicalBounds`,
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_lowerPrev_finiteMaxSourceDenURationalGammaCanonicalBounds`, and
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_lowerPrev_finiteMaxSourceDenURationalGammaCanonicalBounds_solver`
  remove the previous transposed determinant too, deriving it from the
  top-left part of the same `IsDiagDominantUpper` leading block.  The
  stored-lower-zero siblings
  `storedQRPreviousColumnLowerZero_of_stored_trailing_householder_sequence`,
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds`, and
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver`
  then derive the previous-column lower-zero field from the actual stored
  Householder panel recurrence, using the repository prefix lower-zero theorem.
  The corresponding `_of_uCap` siblings remove the separate proof-artifact
  hypothesis `0 <= Ucap`: the FP model has `0 <= fp.u`, so the primitive cap
  `fp.u <= Ucap` already implies `0 <= Ucap`.
  The `_of_uCap_no_gammaValid` siblings go one step further: from
  `fp.u <= Ucap` and `(m : Real) * Ucap < 1` (or `(s : Real) * Ucap < 1`
  at the sampling level) they derive the `gammaValid` guards for the capped
  dimension and, by monotonicity, the triangular dimension.  Thus the cap-based
  public surface no longer asks separately for the gamma-validity hypotheses
  that are already implied by the displayed cap.
  The `_of_actualUnitRoundoff` siblings specialize the displayed cap to the
  actual model value `fp.u`, removing the primitive cap field `fp.u <= Ucap`
  and all `Ucap` notation from this surface.  They still require the ordinary
  `gammaValid` guard and the same canonical scalar smallness condition with
  `Ucap` replaced by `fp.u`; the existing `actualU` counterexample shows that
  this scalar smallness condition is not automatic.  The
  `_of_actualUnitRoundoff_no_gammaValid` siblings replace that remaining
  `gammaValid` guard by the displayed scalar condition `(m : Real) * fp.u < 1`
  or `(s : Real) * fp.u < 1`, deriving the needed validity guards internally
  while keeping scalar smallness visible.
  This is only a cleaner certificate surface; local diagonal dominance/off-diagonal
  control, inverse-factor and pivot-column bounds, primitive `u`/`gamma` caps,
  the numerical scalar inequality itself, and conditioning fields
  remain visible route obligations.  The solver-facing pointwise wrappers
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_diagDominant_finiteMaxNormBudgetCoeffPointwiseBounds_concreteDual`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_finiteMaxNormBudgetCoeffPointwiseBounds_concreteDual`
  compose those per-pivot estimates into the concrete-dual QR solve certificate,
  with the second wrapper deriving leading-block determinant nonzeroness from
  diagonal dominance.  The invariant-level handoff
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxNormBudgetCoeffSmallness`
  and the probability wrapper
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_offDiagonalControl_solver_of_diagDominant_finiteMaxNormBudgetCoeffSmallness`
now compose that coefficient-max scalar condition into the equation (8) sampled
least-squares theorem surface.  The
finite-max source-control,
solver, and RandNLA
objective variants compose that scalar condition into the equation (8) QR
handoff, so the theorem surface no longer needs the raw
`storedQRCompactSequenceProductBudget < 1` assumption on this branch.  The
`κ∞`/dual-budget variants also
reuse the existing leading-block inverse-budget route to derive the
norm-square nonbreakdown margin, so the newest active/prefix source-control
handoff no longer needs `hbudgetNormSq` as a raw hypothesis.
The remaining visible obligations are diagonal lower bounds for rows `i < k`,
local leading-block nonsingularity with the displayed `κ∞`/dual compact-budget
conditions, and deriving the per-pivot or global compact-product smallness
from a concrete pivoted/sorted/off-diagonal loop.
The final equation (8) QR/preconditioner assembly is now a theorem under these
visible domain assumptions.  The sibling equation (8) theorem
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_solver_of_horizonBudget`
lifts the horizon-clamped budget handoff to the sampled objective layer, so the
probability theorem no longer exposes a samplewise global budget-monotonicity
field beyond the QR stage horizon.  The sibling
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_kappaInf_dualBudget_solver_of_horizonBudget`
combines that same horizon-clamped handoff with the `κ∞`/dual-budget
norm-square nonbreakdown adapter.  The sibling equation (8) theorem
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_kappaInf_dualBudget_solver`
threads the same `κ∞`/dual-budget norm-square adapter through the RandNLA
objective layer.  The active-max-pivot sibling
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_kappaInf_dualBudget_solver`
also derives the raw pivot-maximality field from the finite active max-pivot
policy, and its horizon-clamped sibling
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_kappaInf_dualBudget_solver_of_horizonBudget`
also removes the samplewise global budget-monotonicity field on that active-pivot
route, while still leaving diagonal lower bounds, local determinant/conditioning
budgets, and compact-product smallness explicit.
There is also a diagonal-dominance global-product branch:
`StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_diagDominant_globalProduct`,
`StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_diagDominant_globalProduct`,
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_diagDominant_globalProduct`,
and
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_globalProduct_kappaInf_dualBudget_solver`.
The corresponding finite-max scalar-smallness branch is
`StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_diagDominant_finiteMaxSmallness`,
`StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_diagDominant_finiteMaxSmallness`,
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_diagDominant_finiteMaxSmallness`,
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_diagDominant_finiteMaxSmallness_concreteDual`,
and
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSmallness_kappaInf_dualBudget_solver`.
The direct concrete-dual siblings
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_diagDominant_finiteMaxSmallness_concreteDual`
and
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSmallness_concreteDual_solver`
reuse the repository's diagonal-dominant inverse-budget theorem to remove the
auxiliary `κ`, `K`, and dual compact-budget hypotheses from this branch.
The determinant-free concrete-dual siblings
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_finiteMaxSmallness_concreteDual`
and
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSmallness_concreteDual_solver_of_diagDominant`
also remove the separate local determinant field, since
`IsDiagDominantUpper` already includes upper-triangular shape and nonzero
diagonal entries.
The rational-gamma canonical source-denominator siblings
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_finiteMaxSourceDenURationalGammaCanonicalBounds`
and
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSourceDenURationalGammaCanonicalBounds_solver`
thread the displayed unit-roundoff cap, source denominator nonbreakdown, and
canonical finite-max scalar inequality into the same solver/probability
surfaces.
This branch uses the local `IsDiagDominantUpper` invariant to discharge the
offdiag-row diagonal lower-bound and local determinant fields directly, while
keeping diagonal dominance and either the raw global product condition or the
canonical finite-max scalar smallness inequality visible as source/domain
assumptions.
The RandNLA equation (8) objective theorem now has a direct stored-QR handoff
under the packaged off-diagonal-control invariant, a source-shaped sibling,
an explicit row-budget-control sibling, and a second active/prefix global-product
assembly theorem for the current Cox--Higham route:
`storedQRFinalR`, `storedQRFinalTopRhs`, and `storedQRBackSubSolution` name the
final triangular solve data, and
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_offDiagonalControl_solver`
composes the packaged route-1 invariant into the high-probability rounded
sampled-row objective transfer, while
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_offDiagonalControl_solver_of_diagDominant_finiteMaxSmallness`
first builds that packaged invariant from local diagonal dominance and the
canonical finite-max scalar smallness inequality, and
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_sourceOffDiagonalControl_solver`
does the same after expanding the invariant into source-shaped fields.  The
primitive norm-square/off-diagonal-product sibling
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_leadingBlock_det_ne_zero_normSqBudget_offdiag_product_solver`
builds that source-shaped certificate from leading-block determinant
nonzeroness, dimensioned norm-square nonbreakdown, row-wise off-diagonal
domination, and per-pivot compact-product smallness.  The new
row-budget-control theorem
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_solver`
pushes the named `StoredQRDisplayedRowBudgetControl` certificate all the way to
the high-probability equation (8) objective statement, while still keeping
leading-block nonsingularity, norm-square nonbreakdown, and compact-product
smallness visible.  Its `kappaInf_dualBudget` sibling
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_kappaInf_dualBudget_solver`
removes the raw norm-square nonbreakdown hypothesis by deriving it from the
local leading-block `κ∞`/self-norm and dual compact-budget route, while still
leaving the row-budget certificate, leading-block determinant, and
compact-product smallness visible.  The finite-global-product sibling
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_globalProduct_kappaInf_dualBudget_solver`
replaces the per-pivot compact-product family on this packaged row-budget
surface by the scalar condition `storedQRCompactSequenceProductBudget < 1`.
The scalar row-max-defect sibling
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowMaxDiagDefect_globalProduct_solver`
builds the samplewise row-budget certificate from
`storedQRRowMaxDiagDefectBudget <= 0` and the same finite global product
condition, while keeping determinant and norm-square nonbreakdown assumptions
visible.
Its actual-unit-roundoff no-`gammaValid` sibling
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowMaxDiagDefect_globalProduct_solver_of_actualUnitRoundoff_no_gammaValid`
derives the sampled `gammaValid fp s` and triangular `gammaValid fp n` guards
from `(s : ℝ) * fp.u < 1`; it does not prove the row-defect, determinant,
norm-square, or global-product fields.
At the local solver layer, the matching finite-global-product certificates
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_rowBudgetControl_globalProduct`
and
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_rowBudgetControl_globalProduct`
consume `StoredQRDisplayedRowBudgetControl` directly, replace the per-pivot
product family by the same finite scalar product budget, and in the `κ∞`
sibling derive the raw norm-square nonbreakdown margin from the repository's
local `κ∞`/dual-budget adapter.  They still keep the row-budget certificate,
determinant/conditioning data, dual compact-budget assumptions, and
compact-product smallness visible.
The active-max-pivot global-product sibling
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_globalProduct_activeMaxPivot_kappaInf_dualBudget_solver`
builds the samplewise `StoredQRDisplayedRowBudgetControl` certificate internally
from the finite active max-pivot policy plus the global compact-step constructor,
while still leaving diagonal lower bounds, determinant/conditioning data, and
compact-product smallness explicit.
At the least-squares certificate layer,
`StoredQRDisplayedRowBudgetControl.of_signed_stage_uniformBudget_globalCompactBudget_activeMaxPivot_of_normSqBudget`
and
`StoredQRDisplayedRowBudgetControl.of_signed_stage_uniformBudget_globalCompactBudget_activeMaxPivot_kappaInf_dualBudget`
remove the raw pivot-maximality hypothesis from the global compact-step
row-budget constructors by deriving it from the repository's finite active
max-pivot selector.  These are still scoped package-producing dependencies:
the diagonal lower-bound/nonbreakdown field, determinant/conditioning data, and
compact-product smallness remain visible.
At the local least-squares solver layer, the active-pivot-policy theorem
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_offdiag_rows`
does the same replacement for the active/prefix global-product `κ∞` QR
certificate: the theorem surface uses the policy equation that the displayed
pivot is `householderActiveMaxPivotColumn`, and the raw pivot-max inequality is
derived internally.  This closes the pivot-policy field for the solver-facing
route only; diagonal lower bounds, local determinant/conditioning data, dual
compact-budget assumptions, and compact-product smallness remain explicit.
The same pivot-policy reduction now reaches the scalar stage-diagonal branch:
`storedQRActiveMaxPivotColumn_pivotMax` names the common extractor from the
finite selector policy, the new source-control wrappers with suffix
`_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_stageDiagDefect_offdiag_rows`
consume `storedQRStageDiagLowerDefectBudget <= 0` and the policy equation
instead of raw diagonal-family and pivot-max hypotheses, and the solver-facing
`..._activeMaxPivot_completedColumns_globalProduct_stageDiagDefect_offdiag_rows`
wrapper exposes that combined route locally.  This closes only the
pivot-policy field on the scalar stage-diagonal route; the scalar defect,
determinant/nonbreakdown, conditioning, and product-smallness fields remain
visible.
The row-max visible-assumption sibling of this active-pivot route,
`..._activeMaxPivot_completedColumns_globalProduct_rowMaxDiagDefect_stageBudgetLeRowMax_offdiag_rows`,
replaces the scalar `storedQRStageDiagLowerDefectBudget <= 0` hypothesis by a
nonpositive `storedQRRowMaxDiagDefectBudget` hypothesis together with the
explicit comparison
`stageBudget k <= qrLeadingStrictUpperRowMaxBudget hmn A_hat k hk i` on
displayed rows.  It derives the scalar stage-diagonal condition internally via
the row-max bridge, then reuses the active-pivot stage-diagonal source-control
and solver wrappers.  This is still a visible-assumption surface: it does not
prove the row-max scalar defect or the stage-budget/row-max comparison for a
concrete pivoted loop.
Its local actual-unit-roundoff source-control and solver siblings with suffix
`..._rowMaxDiagDefect_stageBudgetLeRowMax_offdiag_rows_of_actualUnitRoundoff_no_gammaValid`
replace the local `gammaValid` assumptions by the single scalar guard
`(m : ℝ) * fp.u < 1`, deriving validity via `gammaValid_of_u_le_cap` and
`gammaValid_mono`.  The row-max scalar defect, the displayed-row comparison,
determinant/conditioning, dual compact-budget, and compact-product fields
remain visible.
The
theorem
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_solver`
then discharges the source-control certificate from the active/prefix
global compact-step, completed-column, and finite global product handoffs. This
theorem now has the horizon-clamped sibling
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_solver_of_horizonBudget`,
which feeds each sample into the LS.2g-hx source-control wrapper and therefore
does not require samplewise budget monotonicity outside `b <= n`. This
is still not a proof that an arbitrary QR/preconditioner loop satisfies the
remaining diagonal lower-bound, nonbreakdown, and global-product-smallness
fields; it is the equation (8) assembly once those fields are supplied.
The active-max-pivot probability wrapper
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_kappaInf_dualBudget_solver`
uses the samplewise policy equation
`t = householderActiveMaxPivotColumn t t (A_hat samples t)` to recover the raw
pivot-max hypothesis from `householderActiveMaxPivotColumn_pivot_max` before
applying the same active/prefix global-product `κ∞` theorem.  Its
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_kappaInf_dualBudget_solver_of_horizonBudget`
sibling uses the LS.2g-hz horizon route, so this active-pivot theorem surface no
longer needs the samplewise global budget-monotonicity field.
The probability-level row-max sibling
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver`
threads the row-max visible assumptions through the same equation (8) theorem:
samplewise `storedQRRowMaxDiagDefectBudget <= 0` and
`stageBudget <= qrLeadingStrictUpperRowMaxBudget` derive the diagonal
lower-bound family internally, while determinant/conditioning, dual
compact-budget, active-pivot policy, and compact-product smallness remain
visible.  Its
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver_of_horizonBudget`
sibling uses the LS.2g-ia active-pivot horizon route, so this visible row-max
probability surface also drops the samplewise global budget-monotonicity field.
Its actual-unit-roundoff sibling
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver_of_actualUnitRoundoff_no_gammaValid`
replaces the sampled `gammaValid` fields by the scalar guard
`(s : ℝ) * fp.u < 1`, deriving `gammaValid fp s` and `gammaValid fp n`
internally via `gammaValid_of_u_le_cap` and `gammaValid_mono`.
The horizon actual-unit sibling
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver_of_actualUnitRoundoff_no_gammaValid_of_horizonBudget`
combines those two reductions, so the visible row-max probability surface
uses the scalar actual-unit guard and no longer exposes samplewise global
budget monotonicity.
The scalar-comparison probability siblings
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver`
and
`..._stageRowMaxComparisonDefect_kappaInf_dualBudget_solver_of_actualUnitRoundoff_no_gammaValid`
replace the samplewise displayed comparison family by
`storedQRStageRowMaxComparisonDefectBudget <= 0`, using the finite-max
extractor before applying the visible row-max equation (8) theorem.
The explicit-validity horizon sibling
`..._stageRowMaxComparisonDefect_kappaInf_dualBudget_solver_of_horizonBudget`
keeps the sampled `gammaValid` fields visible but calls the horizon row-max
wrapper after the same finite comparison extraction, so it drops samplewise
global budget monotonicity from the two-scalar surface.
The scalar-comparison actual-unit horizon sibling
`..._stageRowMaxComparisonDefect_kappaInf_dualBudget_solver_of_actualUnitRoundoff_no_gammaValid_of_horizonBudget`
derives the validity fields from `(s : ℝ) * fp.u < 1` and then calls the
explicit-validity horizon wrapper, so this two-scalar probability surface
also drops both sampled validity fields and samplewise global budget
monotonicity.
The diagonal-dominant sampled sibling
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver`
replaces the samplewise determinant and row-max-defect fields by local
diagonal dominance, while keeping the scalar comparison defect,
conditioning/dual compact-budget fields, active-pivot policy, and
compact-product smallness visible.
Its finite-max sibling
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSmallness_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver`
derives the samplewise raw compact-product field from the canonical finite-max
smallness inequality before applying the same equation (8) wrapper.
The concrete-dual finite-max sibling
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSmallness_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_concreteDual_solver`
uses
`storedQRSignedStage_normSqBudget_of_leadingBlock_det_ne_zero_diagDominant_concreteDualProductSequenceBudget`
to remove the samplewise `κ`, `K`, and dual compact-budget fields from this
active branch; local diagonal dominance, the scalar comparison defect,
active-pivot policy, signed-stage recurrence budget, and finite-max smallness
remain visible.
Its actual-unit-roundoff sibling
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSmallness_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_concreteDual_solver_of_actualUnitRoundoff_no_gammaValid`
derives the sampled and triangular `gammaValid` guards from
`(s : Real) * fp.u < 1`, while the local source-control and solver siblings do
the same from `(m : Real) * fp.u < 1`.  This reduces only the validity surface:
sampling laws remain exact mathematical inputs, and the diagonal-dominance,
active-pivot, signed-stage, scalar-comparison, and finite-max obligations are
still visible.
The source-denominator rational-gamma sampled sibling
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver`
uses the local LS.2g-hm source-control certificate samplewise, replacing the
assembled finite-max scalar at equation (8) by source-denominator
nonbreakdown, `fp.u <= Ucap`, `(s : Real) * Ucap < 1`, and the canonical
rational-gamma cap-smallness scalar.
The horizon-clamped sampled sibling
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver_of_horizonBudget`
applies the local source-denominator horizon certificate per trace, so the
sampled surface no longer exposes global stage-budget monotonicity.
Its actual-unit-roundoff siblings
`StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows_of_actualUnitRoundoff_no_gammaValid`,
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows_of_actualUnitRoundoff_no_gammaValid`, and
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver_of_actualUnitRoundoff_no_gammaValid`
specialize `Ucap = fp.u` and derive the local, triangular, or sampled
`gammaValid` guards internally from `(m : Real) * fp.u < 1` or
`(s : Real) * fp.u < 1`, while keeping the actual-unit scalar smallness and QR
loop obligations visible.
The actual-unit and stored-lower horizon siblings
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver_of_actualUnitRoundoff_no_gammaValid_of_horizonBudget`
and
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver_of_actualUnitRoundoff_no_gammaValid_of_horizonBudget`
combine the same clamp with the actual-unit specialization; the stored-lower
version also derives denominator nonbreakdown from the stored recurrence,
signed-alpha definition, and local diagonal dominance.
The witness theorem
`not_forall_diagDominant_implies_stageRowMaxComparisonDefectBudget_nonpos`
rules out a tempting shortcut: local diagonal dominance alone does not force
the scalar stage-budget/row-max comparison defect to be nonpositive.
Its product-smallness strengthening
`not_forall_diagDominant_product_budget_implies_stageRowMaxComparisonDefectBudget_nonpos`
uses the same witness with compact budget `1 / 16`, so diagonal dominance plus
product smallness still cannot hide the comparison scalar.
The active-surface strengthening
`not_forall_diagDominant_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`
adds active-block positivity, the active max-pivot policy, and
active/off-diagonal budget bounds to the same failed route; the scalar
comparison defect remains independent of that current surface.
For the current unpivoted stored-QR theorem family the remaining visible fields
are local leading-block nonsingularity, norm-square nonbreakdown,
row-growth upper budgets with matching diagonal lower bounds, and
compact-product smallness: local counterexamples rule out
deriving them from the ordinary no-pivot recurrence, full rank, determinant
nonzeroness, positive trailing norm, exact QR shape, finite conditioning,
diagonal dominance alone, or product smallness alone.  A stronger paper-level
implementation theorem would need a pivoted/sorted/off-diagonal-controlled QR
theorem family or a source/application class proving those four fields.
`householderTrailingNorm2Sq_pos_of_column_notInPreviousSpan` converts that
invariant into the positive trailing-column norm, and
`fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_sqrt_budget`
combines it with the square-root budget to prove final nonzero stored
diagonal entries.  The companion wrapper
`fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_active_entry_budget`
uses the active-entry bridge to replace that square-root budget by the visible
condition that the compact diagonal update budget is smaller than some active
trailing entry magnitude.  The solver-facing wrapper
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_active_entry_budget`
pushes the same active-entry route into the local least-squares QR certificate.
The corresponding norm-margin wrappers
`fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_trailingNorm2Sq_budget`
and
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_trailingNorm2Sq_budget`
replace the active-entry witness by the dimensioned condition
`m * budget_k^2 < ||A_k(k:m,k)||_2^2`.
The new leading-dual wrappers
`fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_leading_dual_norm_budget`
and
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leading_dual_norm_budget`
replace that norm-square margin by a bounded dual-row condition
`||L_k(last,:)||_2^2 <= K_k` plus `m * budget_k^2 < 1 / K_k`.
The source-faithful leading-dual solver route also has explicit repository
budget wrappers:
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitNormBudget_of_span_nonbreakdown_leading_dual_norm_budget`
chooses `qrSolveFinalGramBudget` and `qrSolveFinalRhsBudget`, while
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_span_nonbreakdown_leading_dual_norm_budget`
also chooses `storedQRCompactSequenceRelativeBudget`.  The remaining visible
assumptions are prefix-span, the leading dual, its norm budget, sign choice,
and the dual compact-smallness inequality.
The local-inverse wrappers
`fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_leadingBlock_leftInverse_norm_budget`
and
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_leftInverse_norm_budget`
construct that dual by padding rows of a local leading-block left inverse and
use the local inverse-row norm budget directly.
The row-norm local-inverse route now also has explicit repository budget
wrappers:
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitNormBudget_of_span_nonbreakdown_leadingBlock_leftInverse_norm_budget`
chooses the final `qrSolveFinal*` radii, and
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_span_nonbreakdown_leadingBlock_leftInverse_norm_budget`
also chooses `storedQRCompactSequenceRelativeBudget`.
The stored-prefix-span companion
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_norm_budget`
removes the separate prefix-span hypothesis from the row-norm route by using
the stored panel recurrence and previous leading-block left inverses.  It still
keeps the previous/current local left inverses, inverse row-norm budget, sign
choice, and compact-smallness inequality visible.
The analogous Frobenius and infinity companions remove the same separate
prefix-span hypothesis from the repository-budgeted inverse-norm branches,
while leaving the inverse-norm and compact-smallness assumptions visible.
The signed-alpha row, Frobenius, and infinity companions also replace the
explicit squared-alpha and sign-choice assumptions by the standard
`signedHouseholderAlpha` definition.
The determinant companions
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_det_ne_zero_leadingBlock_det_ne_zero_norm_budget`,
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_det_ne_zero_leadingBlock_det_ne_zero_frobNorm_budget`,
and
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_det_ne_zero_leadingBlock_det_ne_zero_infNorm_budget`
instantiate those previous/current local inverse witnesses with the repository
`nonsingInv` whenever the previous transposed leading block and current leading
block have nonzero determinant. They still keep the row/Frobenius/infinity
inverse-budget and compact-smallness inequalities visible.
The companion
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_det_ne_zero_leadingBlock_det_ne_zero_kappaInf_selfNorm_budget`
derives the inverse-∞ budget from a visible local `κ∞` bound and the displayed
self-norm squared budget.
The triangular companion
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_upperTriangular_leadingDiag_ne_zero_kappaInf_selfNorm_budget`
derives the previous/current determinant facts from visible upper-triangular
leading shape and nonzero leading diagonal entries.
The Frobenius inverse-norm variants
`fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_leadingBlock_leftInverse_frobNorm_budget`
and
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_leftInverse_frobNorm_budget`
replace that row budget by the stronger reusable condition
`||C_k||_F^2 <= K_k`, using the shared row-versus-Frobenius lemma
`vecNorm2Sq_row_le_frobNorm_sq`.
The infinity-norm variants add the next local inverse-norm bridge:
`frobNormSq_le_nat_mul_infNorm_sq` and
`frobNorm_sq_le_nat_mul_infNorm_sq` prove
`||C_k||_F^2 <= (k+1) ||C_k||_∞^2`, so the QR wrappers
`householderTrailingNorm2Sq_ge_inv_leadingBlock_leftInverse_infNorm_budget`,
`dim_mul_budget_sq_lt_trailingNorm2Sq_of_leadingBlock_leftInverse_infNorm_budget`,
and
`fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_leadingBlock_leftInverse_infNorm_budget`
plus the solver wrapper
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_leftInverse_infNorm_budget`
accept the visible condition
`(k+1) ||C_k||_∞^2 <= K_k`. This still does not derive the inverse norm from
singular values or determinant margins, but it closes the listed bridge from a
local inverse infinity-norm budget to the stored QR and least-squares
certificates.
The determinant-facing variant
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_det_ne_zero_infNorm_budget`
constructs `C_k` as the repository nonsingular inverse of the local leading
block when `det S_k != 0`, while keeping the same visible inverse-∞ budget.
The condition-number-facing variant
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_det_ne_zero_kappaInf_budget`
uses `infNorm_eq_sup_row_sum`,
`kappaInf_eq_infNorm_mul_infNorm`, and
`infNorm_sq_budget_of_kappaInf_le_and_norm_lower` from
`PerturbationTheory.lean` to derive that inverse-∞ budget from a positive
lower bound `rho_k <= ||S_k||_∞`, a local `kappaInf S_k (nonsingInv S_k) <=
kappa_k` condition, and the displayed squared budget
`(k+1)(kappa_k/rho_k)^2 <= K_k`. This is a genuine condition-number route, but
it still keeps the local norm lower bound and condition-number estimate as
visible domain assumptions.
The stronger determinant-based condition-number variant
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_det_ne_zero_kappaInf_selfNorm_budget`
uses `infNorm_pos_of_det_ne_zero` and
`infNorm_sq_budget_of_kappaInf_le_and_det_ne_zero` to set
`rho_k = ||S_k||_∞`; hence it removes the separate `rho_k` hypothesis while
keeping `det S_k != 0`, the local `kappaInf` bound, and the displayed
`(k+1)(kappa_k / ||S_k||_∞)^2 <= K_k` budget visible.
The prefix-span variant
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_leading_blocks_det_ne_zero_kappaInf_selfNorm_budget`
additionally derives the abstract prefix-span invariant from nonzero
determinants of the previous transposed leading blocks plus the stored
lower-zero shape, while still keeping local determinant, local `kappaInf`,
sign-choice, compact-update, and final solver budgets visible.
The triangular self-norm variant
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_triangular_leading_blocks_kappaInf_selfNorm_budget`
derives those previous/current determinant hypotheses and the completed-column
lower-zero shape from a visible upper-triangular local shape plus nonzero
previous/current leading diagonals. It still keeps the local `kappaInf`,
sign-choice, compact-update, and final solver budgets as domain assumptions.
The prefix-lower-zero variant
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_prefix_lower_zero_triangular_leading_blocks_kappaInf_selfNorm_budget`
derives the needed triangular entries from the stored-loop theorem
`fl_householderStoredPanel_sequence_prefix_lower_zero`, so it no longer asks
for a whole-panel triangular invariant at every intermediate step.
The diagonal-dominant triangular inverse route now reuses the local
`InverseBounds.lean` Higham §8.3 formalization:
`triInv_infNorm_upperBound` proves
`||U^{-1}||_∞ <= 2^(d-1)/min_i |u_ii|`, and
`triInv_infNorm_sq_budget_of_diagDominantUpper` converts that estimate into
the squared budget consumed by the QR route.  The determinant-facing adapter
`triInv_infNorm_sq_budget_of_diagDominantUpper_det_ne_zero` uses the local
`nonsingInv` bridge to remove the explicit inverse witness when
`det U != 0`.  The solver wrappers
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_diagDominant_leadingBlock_invNorm_budget`
and
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_diagDominant_leadingBlock_det_ne_zero_invNorm_budget`
therefore replace the abstract inverse-∞ budget by explicit local
diagonal-dominance, determinant/full-inverse, and diagonal-minimum budget
hypotheses.  They do not prove that the computed leading blocks are diagonal
dominant.
The remaining implementation work is deriving the needed
determinant/rank facts and budget lower bounds from a formal full-rank,
nonbreakdown, or conditioning assumption for the computed triangular factor.
The route-A
common rounded panel/update shape is now explicit as well:
`HouseholderPanelAppError` requires one shared perturbation matrix `Delta P`
for the matrix-panel and right-hand-side updates, and the corresponding
geometric theorem feeds any sequence of such contracts into the common-`Q`
rectangular accumulation result. A later source audit showed that the standard
Householder QR proof is actually columnwise: each panel column and the
right-hand side may use its own vector-level perturbation, while the exact
reflector sequence still gives one theoretical accumulated `Q`. The
source-faithful interface is therefore
`HouseholderColumnwisePanelAppError`, with
`rect_orthogonal_columnwise_vector_sequence_geometric` and
`householderColumnwisePanelAppError_rect_orthogonal_columnwise_vector_sequence_geometric`
providing the columnwise geometric accumulation. This still leaves the
solver/preconditioner theorem open only at the nonzero diagonal, conditioning,
and compact-smallness obligations needed by triangular solves; the stored
columnwise final factorization and `[R;0]` shape assembly itself is now closed
by `fl_householderStoredTrailingPanel_higham_columnwise_factorization`.  The
exact algebraic adapter from a normwise vector forward-error bound to
`HouseholderAppError`, and from per-column
forward-error bounds to the columnwise panel contract, is now closed.  A
concrete explicit-matrix route is also closed:
`fl_householderApplyExplicit` reuses `fl_matVec` to apply an already formed
reflector and proves both the normwise forward-error bound and the
`HouseholderAppError`/columnwise-panel contracts.  This does not replace the
compact Householder update theorem for production QR, but it is a real local
rounded-application dependency for implementations that form `P`.  The compact
dot/scale/subtract route is now formalized separately by
`fl_householderApplyCompact_componentwise_error_bound` and
`fl_householderApplyCompact_forward_error_bound`, with an explicit
data-dependent budget
`householderCompactComponentBudget`; the adapter
`fl_householderApplyCompact_HouseholderAppError_of_budget` converts that
budget into the existing `HouseholderAppError` contract whenever the visible
budget norm is dominated by `c * ||b||_2`.  The sequence adapter
`fl_householderApplyCompactPanel_rect_orthogonal_columnwise_vector_sequence_geometric`
now plugs compact panel/RHS updates into the existing columnwise geometric
accumulation theorem.  The bridge
`LSQRSolveBackwardError.of_compact_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget`
now also converts such a compact sequence into the local least-squares QR
backward-error specification once the final `[R;0]` shape, top-RHS linkage,
upper-triangular/nonzero-diagonal conditions, and induced Gram/RHS budget
bounds are supplied.  The remaining QR work is the implementation-specific
proof that the concrete trailing-reflector loop supplies the stored-step
preservation/zeroing hypotheses, plus the diagonal nonzero/rank proof for the
actual rectangular Householder/preconditioner loop.
The repository now
constructs an
orthonormal basis `U` for the finite augmented data span
`span{columns(A), b}`, proves coordinates for the columns of `[A b]`, and uses
the canonical coordinates `y(x) = U^T (A x - b)` to prove the sampled objective
identity
`f_tilde(x) = ||y(x)||_2^2 + y(x)^T (U_tilde^T U_tilde - I) y(x)` and the
corresponding high-probability sketched-minimizer theorem at dimension
`d = finrank span{columns(A), b}`. The strongest version uses the same two
explicit Bennett sample-budget inequalities as the Algorithm 2 equation (7)
finite-Loewner theorem and assumes `d > 1`. The same augmented-span coordinate
discharge is now available for the fully floating-point Gram transfer, with the
row-scaling and dot-product budget folded into the preservation radius. The
remaining paper-level gap for equation (8) is deriving the QR backward-error
spec, perturbed-Gram certificate, or forward-error certificate from a concrete
downstream FP solver/preconditioner pipeline, plus separate random-projection
variants. As a
fallback, the identity basis `U = I_m` is also
formalized; it gives uniform equation (6) row probabilities and discharges the
column-space condition, but with dimension parameter `d = m` rather than the
augmented-span dimension.

```lean
#check lsResidual
#check lsObjective
#check lsNormalMatrix
#check lsNormalRhs
#check IsLeastSquaresMinimizer
#check IsLeastSquaresApproxMinimizer
#check isLeastSquaresApproxMinimizer_of_minimizer
#check PreservesLSObjective
#check rowSampleLSMatrixWithBasisScale
#check rowSampleLSVectorWithBasisScale
#check fl_rowSampleLSMatrixWithBasisScale
#check fl_rowSampleLSVectorWithBasisScale
#check fl_rowSampleLSMatrixWithBasisScale_error_bound
#check fl_rowSampleLSVectorWithBasisScale_error_bound
#check fl_rowSampleLSResidualWithBasisScale_error_bound
#check fl_rowSampleLSResidualWithBasisScale_error_bound_of_positiveProb
#check lsObjective_residual_difference_bound
#check lsObjective_residual_budget_bound
#check rowSampleLSResidualFpBudget
#check rowSampleLSResidualFpBudget_nonneg
#check rowSampleLSObjectiveFpBudget
#check rowSampleLSObjectiveFpBudget_nonneg
#check fl_rowSampleLSObjectiveWithBasisScale_error_bound_of_positiveProb
#check fl_rowSampleLSObjectiveWithBasisScale_error_bound_of_positiveProb_budget
#check lsObjective_le_of_sketch_preserves_with_objective_error
#check lsObjective_le_one_add_eta_of_sketch_preserves_with_objective_error
#check lsObjective_le_of_sketch_preserves_with_objective_error_and_solver_gap
#check lsObjective_le_one_add_eta_of_sketch_preserves_with_objective_error_and_solver_gap
#check eventProb_lsObjective_le_one_add_eta_of_preserves_with_objective_error
#check eventProb_lsObjective_le_one_add_eta_of_preserves_with_pointwise_objective_error
#check eventProb_lsObjective_le_one_add_eta_of_preserves_with_objective_error_on_event
#check eventProb_lsObjective_le_one_add_eta_of_preserves_with_objective_error_and_solver_gap_on_event
#check eventProb_lsObjective_le_one_add_eta_of_coordinate_finiteLoewner_error_with_objective_error_on_event
#check eventProb_lsObjective_le_one_add_eta_of_coordinate_finiteLoewner_error_with_objective_error_and_solver_gap_on_event
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_solver_gap
#check lsSolutionForwardResidualBudget
#check lsSolutionForwardObjectiveGap
#check lsResidual_difference_bound_of_solution_abs_le
#check lsObjective_solution_forward_error_bound
#check isLeastSquaresApproxMinimizer_of_solution_abs_le
#check gramForwardSolverDx
#check gramForwardSolverDx_nonneg
#check gram_forward_error_certificate_of_perturbed_gram_system
#check rectLSGram
#check rectLSRhs
#check RectLSNormalEquations
#check RectLSNormalEquations.of_rowwise_normal
#check RectLSNormalEquations.of_top_solve_zero_bottom
#check rectTopBlock
#check rectTopBlock_top
#check rectTopBlock_bottom
#check rectTopBlock_add
#check rectTopBlock_frobNorm_perturb_bound
#check rectTopBlock_frobNorm_perturb_bound_of_gamma
#check RectLSNormalEquations.exists_topBlock_of_fl_backSub
#check RectLSNormalEquations.exists_original_perturbation_of_commonQ_topBlock_fl_backSub
#check RectLSNormalEquations.exists_original_perturbation_of_commonQ_topBlock_fl_backSub_gamma_bound
#check LSQRSolveBackwardError.of_commonQ_topBlock_fl_backSub_gamma_bound_normBudget
#check LSQRSolveBackwardError.of_rect_orthogonal_sequence_topBlock_fl_backSub_gamma_bound_normBudget
#check rectLSGramPerturbation
#check rectLSRhsPerturbation
#check rectLSGramPerturbationEntryBudget
#check rectLSRhsPerturbationEntryBudget
#check rectLSGramPerturbationNormBudget
#check rectLSRhsPerturbationNormBudget
#check rectLSGramPerturbation_abs_le_entryBudget
#check rectLSRhsPerturbation_abs_le_entryBudget
#check rectLSGramPerturbation_frobNorm_le_entryBudget
#check rectLSGramPerturbation_abs_le_normBudget
#check rectLSRhsPerturbation_abs_le_normBudget
#check rectLSGramPerturbation_frobNorm_le_normBudget
#check rectLSNormalEquations_perturbed_to_gram_system
#check LSQRSolveBackwardError.of_rectangular_perturbed_normal_equations
#check LSQRSolveBackwardError.of_rectangular_perturbed_normal_equations_normBudget
#check rect_orthogonal_sequence_one_step
#check rect_orthogonal_sequence_geometric
#check orthogonal_vector_sequence_one_step
#check orthogonal_vector_sequence_geometric
#check rect_orthogonal_matrix_vector_sequence_one_step
#check rect_orthogonal_matrix_vector_sequence_geometric
#check householder_row_eq_id_of_zero_prefix
#check householder_col_eq_id_of_zero_prefix
#check matMulVec_householder_eq_self_of_zero_prefix
#check matMul_householder_eq_self_row_of_zero_prefix
#check matMulRectLeft_householder_eq_self_row_of_zero_prefix
#check householderActiveVector
#check householderBeta
#check householderActiveVector_inner_self_eq_two_inner_x
#check householderBeta_mul_activeVector_inner_x
#check matMulVec_householder_activeVector_eq_alpha_basis
#check matMulVec_householder_activeVector_eq_zero_of_ne
#check householderTrailingActiveVector
#check householderTrailingActiveVector_zero_prefix
#check matMulVec_householder_eq_self_of_zero_prefix_support
#check householderTrailingNorm2Sq_pos_of_exists_ne
#check householderTrailingNorm2Sq_pos_of_pivot_ne_zero
#check householderTrailingPivotCounterexample2
#check householderTrailingPivotCounterexample2_pivot_zero
#check householderTrailingPivotCounterexample2_trailingNorm2Sq_pos
#check not_forall_trailingNorm2Sq_pos_implies_pivot_ne_zero
#check householderTrailingNorm2Sq_pos_of_nonneg_budget_lt_sqrt
#check abs_alpha_eq_sqrt_trailingNorm2Sq
#check budget_lt_abs_alpha_of_lt_sqrt_trailingNorm2Sq
#check abs_entry_le_sqrt_householderTrailingNorm2Sq_of_pivot_le
#check budget_lt_sqrt_householderTrailingNorm2Sq_of_lt_abs_active_entry
#check exists_active_entry_budget_lt_abs_of_dim_mul_budget_sq_lt_trailingNorm2Sq
#check budget_lt_sqrt_householderTrailingNorm2Sq_of_dim_mul_budget_sq_lt_trailingNorm2Sq
#check householderTrailingNorm2Sq_ge_inv_leading_dual_norm_budget
#check dim_mul_budget_sq_lt_trailingNorm2Sq_of_leading_dual_norm_budget
#check householderTrailingNorm2Sq_ge_inv_leadingBlock_leftInverse_row_norm_budget
#check dim_mul_budget_sq_lt_trailingNorm2Sq_of_leadingBlock_leftInverse_row_norm_budget
#check qrPreviousColumn
#check qrLeadingColumn
#check qrPrefixRow
#check qrLeadingRow
#check vecNorm2Sq_qrLeadingRow_padded_eq
#check qrColumnNotInPreviousSpan
#check qrPrefixSupportSpannedByPreviousColumns
#check qrPrefixBasisCoefficientMatrix
#check qrPreviousLeadingBlockTranspose
#check qrLeadingBlock
#check qrPrefixBasisCoefficientMatrix_of_leftInverse_previousLeadingBlockTranspose
#check qrPrefixSupportSpannedByPreviousColumns_of_prefixBasisCoefficientMatrix
#check qrPrefixSupportSpannedByPreviousColumns_of_leftInverse_previousLeadingBlockTranspose
#check fl_householderStoredPanel_sequence_prefixSpan_of_leftInverse_previousLeadingBlockTranspose
#check qrLeadingColumnLeftInverse
#check qrLeadingColumnLeftInverse_of_leftInverse_leadingBlock
#check qrLeadingColumnLeftInverse_padded_row_norm_sq_eq
#check qrColumnNotInPreviousSpan_of_leadingColumnLeftInverse
#check exists_active_trailing_entry_ne_of_column_notInPreviousSpan
#check householderTrailingNorm2Sq_pos_of_column_notInPreviousSpan
#check exists_active_trailing_entry_ne_of_leading_witnesses
#check householderTrailingNorm2Sq_pos_of_leading_witnesses
#check fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_leading_witnesses_sqrt_budget
#check exists_active_trailing_entry_ne_of_leading_block_leftInverses
#check householderTrailingNorm2Sq_pos_of_leading_block_leftInverses
#check fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_leading_block_leftInverses_sqrt_budget
#check nonsingInv
#check isLeftInverse_nonsingInv_of_det_isUnit
#check exists_isLeftInverse_of_det_ne_zero
#check det_ne_zero_of_upper_triangular_diag_ne_zero
#check diag_ne_zero_of_upper_triangular_det_ne_zero
#check det_ne_zero_of_lower_triangular_diag_ne_zero
#check qrPrefixBasisCoefficientMatrix_of_det_ne_zero_previousLeadingBlockTranspose
#check qrLeadingColumnLeftInverse_of_det_ne_zero_leadingBlock
#check qrPreviousLeadingBlockTranspose_det_ne_zero_of_local_lower_triangular_diag_ne_zero
#check qrLeadingBlock_det_ne_zero_of_local_upper_triangular_diag_ne_zero
#check qrPreviousLeadingBlockTranspose_det_ne_zero_of_upper_triangular_diag_ne_zero
#check qrLeadingBlock_det_ne_zero_of_upper_triangular_diag_ne_zero
#check qrPivotCounterexample2_first_pivot_zero
#check qrPivotCounterexample2_det_ne_zero
#check not_forall_det_ne_zero_implies_first_pivot_ne_zero
#check qrPivotCounterexample2_first_leadingBlock_det_zero
#check not_forall_det_ne_zero_implies_all_leading_blocks_det_ne_zero
#check qrLeadingBlock_current_pivot_ne_zero_of_local_upper_triangular_det_ne_zero
#check fl_householderStoredTrailingPanel_sequence_current_pivot_ne_zero_of_leadingBlock_det_ne_zero
#check exists_active_trailing_entry_ne_of_leading_block_det_ne_zero
#check householderTrailingNorm2Sq_pos_of_leading_block_det_ne_zero
#check fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_leading_block_det_ne_zero_sqrt_budget
#check signedHouseholderAlpha
#check signedHouseholderAlpha_sqrt_trailingNorm2Sq_sq
#check signedHouseholderAlpha_sqrt_trailingNorm2Sq_mul_pivot_nonpos
#check householderTrailingActiveVector_inner_self_ne_zero_of_pivot_ne_alpha
#check householder_pivot_ne_alpha_of_trailingNorm2Sq_pos_mul_nonpos
#check householderTrailingActiveVector_inner_self_ne_zero_of_trailingNorm2Sq_pos_mul_nonpos
#check householderTrailingActiveVector_inner_self_ge_two_trailingNorm2Sq_of_mul_nonpos
#check householderTrailingActiveVector_inner_self_ge_two_trailingNorm2Sq_signed
#check householderTrailingColumnNorm2Sq
#check exists_householderTrailingColumnNorm2Sq_active_max
#check abs_inner_householderTrailingActiveVector_trailingPart_le_vecNorm2_mul_sqrt
#check abs_inner_householderTrailingActiveVector_column_le_vecNorm2_mul_sqrt_of_pivot_max
#check abs_two_div_mul_le_sqrt_two_of_abs_le_sqrt_mul_sqrt
#check householderBeta_mul_inner_self_eq_two
#check abs_householderBeta_mul_inner_trailingPart_le_sqrt_two_of_mul_nonpos
#check abs_householderBeta_mul_inner_trailingPart_le_sqrt_two_signed
#check abs_householderBeta_mul_inner_column_le_sqrt_two_of_signed_pivot_max
#check abs_sub_mul_le_one_add_sqrt_two_mul_bound
#check abs_householder_signed_pivot_update_entry_le_one_add_sqrt_two_mul_row_bound
#check coxHighamGrowthFactor_nonneg
#check scalar_growth_iterate_bound
#check coxHigham_rowSorting_active_entry_bound_of_prior_growth
#check coxHigham_rowSorting_active_entry_bound_of_stage_growth
#check coxHigham_pivot_row_entry_bound_of_active_tail_entry_bound
#check coxHigham_pivot_row_entry_bound_of_stage_entry_bound
#check abs_matMulVec_householder_pivot_le_trailing_vecNorm2_of_zero_prefix_orthogonal
#check coxHigham_signed_pivot_row_update_abs_le_trailing_vecNorm2
#check coxHigham_exact_signed_pivot_row_entry_bound_of_stage_entry_bound
#check scalarAffineGrowthBudget
#check scalar_affine_growth_iterate_bound
#check coxHigham_rowSorting_active_entry_bound_of_stage_growth_with_additive
#check coxHigham_rowwise_error_accumulation_bound
#check coxHigham_abs_entry_le_exact_bound_add_error
#check coxHigham_rowSorting_active_entry_bound_with_accumulated_error
#check fl_householderStoredPanelStep_active_entry_componentwise_error_bound
#check coxHigham_storedPanelStep_row_error_recurrence_of_exact_lipschitz
#check coxHigham_storedPanel_sequence_rowwise_error_accumulation_bound_of_exact_lipschitz
#check matMulVec_householder_signed_pivot_update_entry_eq
#check coxHigham_exact_same_reflector_row_growth_of_signed_pivot_row_bound
#check coxHigham_exact_signed_pivot_active_row_entry_bound_of_stage_bounds
#check coxHighamActiveRowGrowthFactor
#check coxHighamActiveRowGrowthFactor_nonneg
#check one_le_coxHighamActiveRowGrowthFactor
#check exactSignedPivotHouseholderPanelStep
#check coxHigham_exactSignedPivotPanelStep_active_entry_bound_of_stage_bounds
#check coxHigham_exactSignedPivotPanelStep_active_block_bound_of_stage_bound
#check coxHigham_exactSignedPivotPanel_sequence_active_entry_bound_of_stage_budgets
#check coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_stage_budgets
#check coxHigham_exactSignedPivotPanel_sequence_active_entry_bound_of_geometric_stage_budgets
#check coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_geometric_stage_budgets
#check coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound
#check householderActiveMaxPivotColumn
#check householderActiveMaxPivotColumn_ge
#check householderActiveMaxPivotColumn_pivot_max
#check householderSwapColumns
#check householderTrailingColumnNorm2Sq_swapColumns_left
#check householderTrailingColumnNorm2Sq_swapColumns_of_ne
#check householderSwapColumns_activeMaxPivotColumn_pivot_max
#check householderActiveBlockNorm2Sq
#check exists_active_entry_ne_of_householderActiveBlockNorm2Sq_pos
#check householderActiveBlockNorm2Sq_pos_of_exists_active_entry_ne
#check householderActiveBlockNorm2Sq_swapColumns_pos_of_pos
#check householderTrailingColumnNorm2Sq_pos_of_pivot_max_exists_pos
#check householderTrailingColumnNorm2Sq_pos_of_pivot_max_exists_active_entry_ne
#check coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_active_block_nonzero
#check coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_active_max_pivot
#check coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_active_block_norm_pos
#check coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_swapped_active_max_pivot
#check coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_swapped_active_max_pivot_of_raw_active_block_norm_pos
#check coxHigham_storedPanelStep_active_entry_bound_of_exact_growth
#check coxHigham_storedPanel_sequence_active_entry_bound_of_exact_growth
#check coxHigham_storedPanelStep_active_entry_bound_of_exact_growth_factor
#check coxHigham_storedPanel_sequence_active_entry_bound_of_exact_growth_factor
#check coxHigham_storedPanel_sequence_active_entry_bound_of_exact_active_growth
#check coxHigham_storedPanelStep_active_entry_bound_of_exact_stage_budget_factor
#check coxHigham_storedPanel_sequence_active_entry_bound_of_exact_stage_budgets_factor
#check coxHigham_storedPanel_sequence_active_entry_bound_of_exact_active_stage_budgets
#check coxHigham_storedPanelStep_active_entry_bound_of_signed_pivot_stage_bounds
#check signedPivotHouseholderVector
#check signedPivotHouseholderBeta
#check coxHigham_storedPanel_sequence_active_block_bound_of_signed_pivot_stage_bounds
#check qrLeadingOffdiagStop
#check storedQRSignedStageVector
#check storedQRSignedStageBeta
#check storedQRSignedStage_exact_same_reflector_bound_of_prefix_or_active_stage_bounds
#check fl_householderStoredPanel_sequence_completed_column_eq_pivot_succ
#check fl_householderStoredPanel_sequence_leadingBlock_offdiag_budget_of_exact_stage_budgets_factor
#check fl_householderStoredPanel_sequence_leadingBlock_offdiag_budget_of_signed_stage_budgets_factor
#check storedQRSignedStage_pivot_column_zero_below_of_trailingNorm_pos
#check storedQRSignedStage_pivot_zeroing_field_of_trailingNorm_pos
#check storedQRSignedStage_pivot_zeroing_field_of_normSqBudget
#check StoredQRDisplayedRowBudgetControl
#check StoredQRDisplayedRowBudgetControl.of_signed_stage_budgets_factor_of_normSqBudget
#check qrLeadingStrictUpperRowMaxBudget
#check qrLeadingStrictUpperRowMaxBudget_entry_le
#check qrLeadingStrictUpperRowMaxBudget_le_diag_of_offdiag
#check storedQRRowMaxDiagDefectBudget
#check storedQRRowMaxDiagDefect_le_budget
#check storedQRRowMaxDiagDefectBudget_nonpos_of_diagDominant
#check StoredQRDisplayedRowBudgetControl.of_diagDominant
#check StoredQRDisplayedRowBudgetControl.of_rowMaxDiagDefectBudget_nonpos
#check storedQRStageDiagLowerDefectBudget
#check storedQRStageDiagLowerDefect_le_budget
#check storedQRStageBudget_le_diag_of_stageDiagLowerDefectBudget_nonpos
#check storedQRStageDiagLowerDefectBudget_nonpos_of_stageBudget_le_diag
#check storedQRStageDiagLowerDefectBudget_nonpos_of_rowMaxDiagDefectBudget_nonpos_stageBudget_le_rowMax
#check storedQRStageDiagLowerDefectBudget_nonpos_of_diagDominant_stageBudget_le_rowMax
#check storedQRStageRowMaxComparisonDefectBudget
#check storedQRStageRowMaxComparisonDefect_le_budget
#check storedQRStageBudget_le_rowMax_of_stageRowMaxComparisonDefectBudget_nonpos
#check storedQRStageRowMaxComparisonDefectBudget_nonpos_of_stageBudget_le_rowMax
#check storedQRStageRowMaxComparisonDefectBudget_nonpos_of_horizonBudget
#check storedQRStageDiagLowerDefectBudget_nonpos_of_rowMaxDiagDefectBudget_nonpos_stageRowMaxComparisonDefectBudget_nonpos
#check storedQRStageDiagLowerDefectBudget_nonpos_of_diagDominant_stageRowMaxComparisonDefectBudget_nonpos
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_rowMaxDiagDefect_globalProduct_of_actualUnitRoundoff_no_gammaValid
#check exactHouseholderQRDiagDominanceCounterexample_rowMaxDiagDefectBudget_pos
#check not_forall_exact_trailing_householder_sequence_implies_rowMaxDiagDefectBudget_nonpos
#check activeMaxPivotRowBudgetDiagCounterexample_rowMaxDiagDefectBudget_pos
#check not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_rowMaxDiagDefectBudget_nonpos
#check not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_stageRowMaxComparisonDefectBudget_nonpos
#check not_forall_leadingBlock_upper_det_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_stageRowMaxComparisonDefectBudget_nonpos
#check activeMaxPivotRowMaxComparisonCounterexample_diagDominant
#check not_forall_diagDominant_implies_stageRowMaxComparisonDefectBudget_nonpos
#check activeMaxPivotRowMaxComparisonCounterexample_productBudget
#check not_forall_diagDominant_product_budget_implies_stageRowMaxComparisonDefectBudget_nonpos
#check not_forall_diagDominant_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_stageRowMaxComparisonDefectBudget_nonpos
#check activeMaxPivotRowMaxComparisonCounterexample_rowMaxDiagDefectBudget_nonpos
#check activeMaxPivotRowMaxComparisonCounterexample_stageRowMaxComparisonDefectBudget_pos
#check activeMaxPivotRowMaxComparisonCounterexample_stageDiagLowerDefectBudget_pos
#check not_forall_rowMaxDiagDefectBudget_implies_stageDiagLowerDefectBudget_nonpos
#check not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_rowMaxDiagDefect_implies_stageDiagLowerDefectBudget_nonpos
#check not_forall_leadingBlock_upper_det_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_rowMaxDiagDefect_implies_stageDiagLowerDefectBudget_nonpos
#check not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_rowMaxDiagDefect_implies_stageRowMaxComparisonDefectBudget_nonpos
#check not_forall_leadingBlock_upper_det_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_rowMaxDiagDefect_implies_stageRowMaxComparisonDefectBudget_nonpos
#check exactHouseholderQRDiagDominanceCounterexample_stageDiagLowerDefectBudget_pos
#check not_forall_exact_trailing_householder_sequence_implies_stageDiagLowerDefectBudget_nonpos
#check exactHouseholderQRDiagDominanceCounterexample_stageRowMaxComparisonDefectBudget_pos
#check not_forall_exact_trailing_householder_sequence_implies_stageRowMaxComparisonDefectBudget_nonpos
#check not_forall_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_implies_stageDiagLowerDefectBudget_nonpos
#check not_forall_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos
#check storedDiagDominantComparisonCounterexample_stored_step
#check storedDiagDominantComparisonCounterexample_rhs_step
#check storedDiagDominantComparisonCounterexample_diagDominant
#check storedDiagDominantComparisonCounterexample_activeMaxPivotChoice
#check storedDiagDominantComparisonCounterexample_compactSequenceRelativeBudget_eq_zero
#check storedDiagDominantComparisonCounterexample_compactSequenceProductBudget_lt_one
#check storedDiagDominantComparisonCounterexample_finiteMaxSmallness
#check storedDiagDominantComparisonCounterexample_globalBudgetStageBudget_nonneg
#check storedDiagDominantComparisonCounterexample_globalCompactBudget_eq_zero
#check storedDiagDominantComparisonCounterexample_globalCompactBudget_recurrence
#check storedDiagDominantComparisonCounterexample_stageRowMaxComparisonDefectBudget_pos_globalBudgetStageBudget
#check storedDiagDominantComparisonCounterexample_rowMaxDiagDefectBudget_nonpos
#check storedDiagDominantComparisonCounterexample_leadingBlock_det_ne_zero
#check storedDiagDominantComparisonCounterexample_compactComponentBudget_eq_zero
#check storedDiagDominantComparisonCounterexampleKappaBudget
#check storedDiagDominantComparisonCounterexampleKappaNormSqBudget
#check storedDiagDominantComparisonCounterexample_kappaBudget_le
#check storedDiagDominantComparisonCounterexample_kappaNormSqBudget_pos
#check storedDiagDominantComparisonCounterexample_kappaNormSqBudget
#check storedDiagDominantComparisonCounterexample_dualBudget
#check storedDiagDominantComparisonCounterexampleFinalSurfaceStageBudget
#check storedDiagDominantComparisonCounterexample_finalSurfaceStageBudget_nonneg
#check storedDiagDominantComparisonCounterexample_finalSurfaceStageBudget_mono
#check storedDiagDominantComparisonCounterexample_finalSurface_init
#check storedDiagDominantComparisonCounterexample_finalSurface_initBlock
#check storedDiagDominantComparisonCounterexample_finalSurface_globalCompactBudget_recurrence
#check storedDiagDominantComparisonCounterexample_stageRowMaxComparisonDefectBudget_pos_finalSurfaceStageBudget
#check storedDiagDominantComparisonCounterexample_finalSurface_sourceDenURationalGammaCanonicalSmallness
#check storedDiagDominantComparisonCounterexample_stageDiagLowerDefectBudget_pos
#check storedDiagDominantComparisonCounterexample_stageRowMaxComparisonDefectBudget_pos
#check not_forall_diagDominant_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageDiagLowerDefectBudget_nonpos
#check not_forall_diagDominant_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos
#check not_forall_diagDominant_activeMaxPivot_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos
#check not_forall_diagDominant_activeMaxPivot_product_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos
#check not_forall_diagDominant_activeMaxPivot_finiteMaxSmallness_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos
#check not_forall_diagDominant_activeMaxPivot_globalCompactBudget_finiteMaxSmallness_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos
#check not_forall_diagDominant_activeMaxPivot_globalCompactBudget_finiteMaxSmallness_rowMaxDiagDefect_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos
#check not_forall_diagDominant_activeMaxPivot_leadingBlock_det_ne_zero_globalCompactBudget_finiteMaxSmallness_rowMaxDiagDefect_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos
#check not_forall_diagDominant_activeMaxPivot_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_globalCompactBudget_finiteMaxSmallness_rowMaxDiagDefect_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos
#check not_forall_diagDominant_activeMaxPivot_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_init_globalProduct_globalCompactBudget_rowMaxDiagDefect_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonneg_monoStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos
#check not_forall_diagDominant_activeMaxPivot_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_init_sourceDenURationalGammaCanonical_globalCompactBudget_rowMaxDiagDefect_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonneg_monoStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos
#check StoredQRDisplayedRowBudgetControl.of_sourceOffDiagonalControl_rowMaxBudget
#check StoredQRDisplayedRowBudgetControl.of_signed_stage_uniformBudget_factor_of_normSqBudget
#check StoredQRDisplayedRowBudgetControl.of_signed_stage_uniformBudget_globalCompactBudget_of_normSqBudget
#check StoredQRDisplayedRowBudgetControl.of_signed_stage_uniformBudget_globalCompactBudget_kappaInf_dualBudget
#check storedQRActiveMaxPivotColumn_pivotMax
#check StoredQRDisplayedRowBudgetControl.of_signed_stage_uniformBudget_globalCompactBudget_activeMaxPivot_of_normSqBudget
#check StoredQRDisplayedRowBudgetControl.of_signed_stage_uniformBudget_globalCompactBudget_activeMaxPivot_kappaInf_dualBudget
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_rowBudget_product_of_offdiag_rows
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_rowBudget_product_of_offdiag_rows
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_rowBudgetControl_product
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_rowBudgetControl_globalProduct
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_rowBudgetControl_product
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_stageBudget_rowBudget_product_of_offdiag_rows
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_stageBudget_rowBudget_product_of_offdiag_rows
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageBudget_rowBudget_product_of_offdiag_rows
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageBudget_rowBudget_product_of_offdiag_rows
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageBudget_rowBudget_product_of_normSqBudget_offdiag_rows
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageBudget_rowBudget_product_of_normSqBudget_offdiag_rows
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_offdiag_rows
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_offdiag_rows
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_stage_entry_bounds_offdiag_rows
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_stage_entry_bounds_offdiag_rows
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_stage_entry_bounds_offdiag_rows
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_stage_entry_bounds_offdiag_rows
#check storedQRSignedStage_active_block_bound_of_signed_stage_budget
#check storedQRSignedStage_prefix_row_bound_of_active_block_and_prefix_budget
#check storedQRSignedStage_completed_column_preservation
#check storedQRSignedStageGlobalCompactBudget
#check storedQRSignedStage_compact_component_le_globalBudget
#check storedQRSignedStageGlobalCompactBudget_nonneg
#check storedQRSignedStage_active_prefix_budgets_of_globalCompactBudget
#check storedQRSignedStageBudget_mono_on_stages_of_globalCompactBudget
#check qrStageHorizonBudget
#check qrStageHorizonBudget_eq_of_le
#check qrStageHorizonBudget_nonneg
#check qrStageHorizonBudget_mono_of_mono_on_stages
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_globalCompactBudget_completedColumns_globalProduct_offdiag_rows_of_horizonBudget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_globalCompactBudget_completedColumns_globalProduct_offdiag_rows_of_horizonBudget
#check storedQRCompactSequenceProductExpr
#check storedQRCompactSequenceProductBudget
#check storedQRCompactSequenceProductExpr_le_budget
#check storedQRCompactSequenceProductBudget_lt_one_of_forall_expr_lt
#check storedQRCompactSequenceProductBudget_lt_one_of_forall_pivot_product
#check storedQRCompactSequenceProductBudget_lt_one_of_relativeBudget_eq_zero
#check storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_factor_norm_bounds
#check storedQRDiagDominantInvFactorBudget
#check storedQRDiagDominantInvFactor_le_budget
#check storedQRDiagDominantInvFactorBudget_nonneg
#check storedQRPivotColumnNormBudget
#check storedQRPivotColumnNorm_le_budget
#check storedQRPivotColumnNormBudget_nonneg
#check storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_smallness
#check storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_relativeBudget_le
#check storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_stepBudget_le
#check storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_columnRhsBudget_le
#check storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_columnRhsNormBudget_le
#check storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_columnRhsComponentBudget_le
#check storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_normBudgetCoeff_le
#check storedQRCompactStepNormBudgetCoeffBudget
#check storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_normBudgetCoeffBudget
#check StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSmallness
#check not_forall_leadingBlock_upper_det_activeBlockPos_offdiagBudget_implies_rowBudget_diag
#check activeMaxPivotRowBudgetDiagCounterexampleA0
#check activeMaxPivotRowBudgetDiagCounterexampleSeq
#check not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_offdiagBudget_implies_rowBudget_diag
#check not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_rowBudget_diag
#check not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_property_implies_rowBudget_diag
#check not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_rowMaxDiagDefectBudget_nonpos
#check not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_stageBudget_le_rowMax
#check det_ne_zero_of_diagDominantUpper
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_diagDominant_finiteMaxSmallness
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_diagDominant_finiteMaxSmallness
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_diagDominant_finiteMaxSmallness
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_diagDominant_finiteMaxSmallness_concreteDual
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_finiteMaxSmallness_concreteDual
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_finiteMaxSourceDenURationalGammaCanonicalBounds
#check storedQRSourceDenominator_ne_zero_of_trailingNorm2Sq_pos_mul_nonpos
#check StoredQROffDiagonalControlInvariant.of_diagDominant_trailingNormPos_finiteMaxSourceDenURationalGammaCanonicalBounds
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_trailingNormPos_finiteMaxSourceDenURationalGammaCanonicalBounds
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_trailingNormPos_finiteMaxSourceDenURationalGammaCanonicalBounds_solver
#check StoredQROffDiagonalControlInvariant.of_diagDominant_leadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds
#check StoredQROffDiagonalControlInvariant.of_diagDominant_signedAlphaDef_leadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds
#check StoredQROffDiagonalControlInvariant.of_diagDominant_signedAlphaDef_previousLeadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds
#check qrPreviousLeadingBlockTranspose_det_ne_zero_of_diagDominant_leadingBlock
#check StoredQROffDiagonalControlInvariant.of_diagDominant_signedAlphaDef_lowerPrev_finiteMaxSourceDenURationalGammaCanonicalBounds
#check storedQRPreviousColumnLowerZero_of_stored_trailing_householder_sequence
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_leadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_previousLeadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_lowerPrev_finiteMaxSourceDenURationalGammaCanonicalBounds
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_of_uCap
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_of_uCap_no_gammaValid
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_of_actualUnitRoundoff
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_of_actualUnitRoundoff_no_gammaValid
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_leadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds_solver
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_previousLeadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds_solver
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_lowerPrev_finiteMaxSourceDenURationalGammaCanonicalBounds_solver
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver_of_uCap
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver_of_uCap_no_gammaValid
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver_of_actualUnitRoundoff
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver_of_actualUnitRoundoff_no_gammaValid
#check not_forall_diagDominant_sourceDen_uCap_implies_uRationalGammaCanonicalSmallness
#check not_forall_diagDominant_sourceDen_actualU_implies_uRationalGammaCanonicalSmallness
#check not_forall_diagDominant_signedAlphaDef_sourceDen_actualU_implies_uRationalGammaCanonicalSmallness
#check not_forall_diagDominant_signedAlphaDef_sourceDen_actualU_no_gammaValid_implies_uRationalGammaCanonicalSmallness
#check not_forall_diagDominant_signedAlphaDef_stored_trailing_sequence_actualU_no_gammaValid_implies_uRationalGammaCanonicalSmallness
#check storedQRSignedStage_normSqBudget_of_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget
#check storedQRSignedStage_normSqBudget_of_leadingBlock_det_ne_zero_diagDominant_concreteDualProductSequenceBudget
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_offdiag_rows
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_offdiag_rows
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_prefixRowRecurrence_offdiag_rows
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_prefixRowRecurrence_offdiag_rows
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_globalCompactBudget_offdiag_rows
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_globalCompactBudget_offdiag_rows
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_globalCompactBudget_completedColumns_offdiag_rows
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_globalCompactBudget_completedColumns_offdiag_rows
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_globalCompactBudget_completedColumns_globalProduct_offdiag_rows
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_globalCompactBudget_completedColumns_globalProduct_offdiag_rows
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_completedColumns_globalProduct_offdiag_rows
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_completedColumns_globalProduct_offdiag_rows
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_globalCompactBudget_completedColumns_globalProduct_stageDiagDefect_offdiag_rows
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_globalCompactBudget_completedColumns_globalProduct_stageDiagDefect_offdiag_rows
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_completedColumns_globalProduct_stageDiagDefect_offdiag_rows
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_completedColumns_globalProduct_stageDiagDefect_offdiag_rows
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_stageDiagDefect_offdiag_rows
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_stageDiagDefect_offdiag_rows
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_stageDiagDefect_offdiag_rows
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_rowMaxDiagDefect_stageBudgetLeRowMax_offdiag_rows
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_rowMaxDiagDefect_stageBudgetLeRowMax_offdiag_rows_of_actualUnitRoundoff_no_gammaValid
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_rowMaxDiagDefect_stageRowMaxComparisonDefect_offdiag_rows
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_rowMaxDiagDefect_stageRowMaxComparisonDefect_offdiag_rows_of_actualUnitRoundoff_no_gammaValid
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_stageRowMaxComparisonDefect_offdiag_rows
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSmallness_stageRowMaxComparisonDefect_offdiag_rows
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSmallness_stageRowMaxComparisonDefect_concreteDual_offdiag_rows
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows_of_horizonBudget
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows_of_actualUnitRoundoff_no_gammaValid
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_rowMaxDiagDefect_stageBudgetLeRowMax_offdiag_rows
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_rowMaxDiagDefect_stageBudgetLeRowMax_offdiag_rows_of_actualUnitRoundoff_no_gammaValid
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_rowMaxDiagDefect_stageRowMaxComparisonDefect_offdiag_rows
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_rowMaxDiagDefect_stageRowMaxComparisonDefect_offdiag_rows_of_actualUnitRoundoff_no_gammaValid
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_stageRowMaxComparisonDefect_offdiag_rows
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSmallness_stageRowMaxComparisonDefect_offdiag_rows
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSmallness_stageRowMaxComparisonDefect_concreteDual_offdiag_rows
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows_of_actualUnitRoundoff_no_gammaValid
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_stageBudget_rowBudget_product
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_stageBudget_rowBudget_product
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageBudget_rowBudget_product
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageBudget_rowBudget_product
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageBudget_rowBudget_product_of_normSqBudget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageBudget_rowBudget_product_of_normSqBudget
#check qrLeadingOffdiagStop_le
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget
#check StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_stage_entry_bounds
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_stage_entry_bounds
#check matMulVec_householder_trailingActiveVector_eq_prefix_alpha_zero
#check matMulVec_householder_trailingActiveVector_eq_zero_of_pivot_lt
#check exact_trailing_householder_sequence_lower_zero
#check rectangular_topBlock_shape_facts_of_lower_zero
#check fl_householderStoredPanelStep
#check fl_householderStoredRhsStep
#check fl_householderStoredPanel_sequence_prefix_lower_zero
#check fl_householderStoredPanel_sequence_lower_zero
#check fl_householderStoredPanel_sequence_topBlock_shape_facts
#check fl_householderStoredTrailingPanelStep_diag_nonzero_of_budget_lt_abs_alpha
#check fl_householderStoredPanel_sequence_diag_nonzero_of_step_diag_nonzero
#check fl_householderStoredPanel_sequence_prefix_diag_nonzero_of_step_diag_nonzero
#check fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_budget_lt_abs_alpha
#check fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_pivot_ne_alpha
#check fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_trailingNorm_pos_mul_nonpos
#check fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_signed_alpha_trailingNorm_pos_sqrt_budget
#check fl_householderStoredTrailingPanel_sequence_prefix_diag_nonzero_of_signed_alpha_trailingNorm_pos_sqrt_budget
#check fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_sqrt_budget
#check fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_active_entry_budget
#check fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_trailingNorm2Sq_budget
#check fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_leading_dual_norm_budget
#check fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_leadingBlock_leftInverse_norm_budget
#check fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_leadingBlock_leftInverse_frobNorm_budget
#check fl_householderStoredTrailingPanelStep_HouseholderColumnwisePanelAppError_of_budget
#check fl_householderStoredTrailingPanel_rect_orthogonal_columnwise_vector_sequence_geometric
#check fl_householderStoredTrailingPanel_higham_columnwise_factorization
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_pivot_error_lt_abs_alpha
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_pivot_ne_alpha_and_pivot_error_lt_abs_alpha
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_trailingNorm_pos_mul_nonpos_and_pivot_error_lt_abs_alpha
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_signed_alpha_trailingNorm_pos_and_sqrt_budget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_active_entry_budget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_trailingNorm2Sq_budget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leading_dual_norm_budget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitNormBudget_of_span_nonbreakdown_leading_dual_norm_budget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_span_nonbreakdown_leading_dual_norm_budget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_leftInverse_norm_budget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitNormBudget_of_span_nonbreakdown_leadingBlock_leftInverse_norm_budget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_span_nonbreakdown_leadingBlock_leftInverse_norm_budget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_leftInverse_frobNorm_budget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitNormBudget_of_span_nonbreakdown_leadingBlock_leftInverse_frobNorm_budget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_span_nonbreakdown_leadingBlock_leftInverse_frobNorm_budget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_leftInverse_infNorm_budget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitNormBudget_of_span_nonbreakdown_leadingBlock_leftInverse_infNorm_budget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_span_nonbreakdown_leadingBlock_leftInverse_infNorm_budget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_norm_budget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_frobNorm_budget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_infNorm_budget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_norm_budget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_frobNorm_budget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_infNorm_budget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_det_ne_zero_leadingBlock_det_ne_zero_norm_budget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_det_ne_zero_leadingBlock_det_ne_zero_frobNorm_budget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_det_ne_zero_leadingBlock_det_ne_zero_infNorm_budget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_det_ne_zero_leadingBlock_det_ne_zero_kappaInf_selfNorm_budget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_upperTriangular_leadingDiag_ne_zero_kappaInf_selfNorm_budget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_det_ne_zero_infNorm_budget
#check infNorm_pos_of_det_ne_zero
#check infNorm_eq_sup_row_sum
#check kappaInf_eq_infNorm_mul_infNorm
#check infNorm_sq_budget_of_kappaInf_le_and_norm_lower
#check infNorm_sq_budget_of_kappaInf_le_and_det_ne_zero
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_det_ne_zero_kappaInf_budget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_det_ne_zero_kappaInf_selfNorm_budget
#check qrPrefixSupportSpannedByPreviousColumns_of_det_ne_zero_previousLeadingBlockTranspose
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_leading_blocks_det_ne_zero_kappaInf_selfNorm_budget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_triangular_leading_blocks_kappaInf_selfNorm_budget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_prefix_lower_zero_triangular_leading_blocks_kappaInf_selfNorm_budget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_signed_alpha_prefix_lower_zero_triangular_leading_blocks_kappaInf_selfNorm_budget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_signed_alpha_prefix_lower_zero_pivot_nonzero_kappaInf_selfNorm_budget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_pivot_nonzero_kappaInf_selfNorm_normSqBudget
#check qrPrefixSupportSpannedByPreviousColumns_of_leadingBlock_upper_det_ne_zero
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_leadingBlock_det_ne_zero_kappaInf_selfNorm_normSqBudget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_leadingBlock_det_ne_zero_invNorm_dualBudget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_diagDominant_leadingBlock_det_ne_zero_dualBudget
#check diagDominantUpperInvBudgetExpr
#check diagDominantUpperInvBudgetExpr_pos
#check triInv_infNorm_sq_budget_of_diagDominantUpper_det_ne_zero_twice_budget
#check mul_sq_lt_inv_two_mul_of_two_mul_mul_sq_lt_one
#check two_mul_mul_sq_lt_one_of_nonneg_le
#check storedQRCompactPivotBudget_le_sequence_column_norm
#check not_forall_pos_implies_two_mul_mul_sq_lt_one
#check not_forall_diagDominantUpper_implies_two_mul_budget_expr_mul_sq_lt_one
#check not_forall_upper_tri_det_ne_zero_product_budget_implies_diagDominant
#check not_forall_upper_tri_det_ne_zero_product_budget_implies_rowMaxDiagDefectBudget_nonpos
#check not_forall_upper_tri_det_ne_zero_product_budget_implies_stageDiagLowerDefectBudget_nonpos
#check not_forall_leadingBlock_upper_det_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_stageBudget_le_rowMax
#check not_forall_leadingBlock_upper_det_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_rowMaxDiagDefectBudget_nonpos
#check not_forall_leadingBlock_upper_det_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_stageDiagLowerDefectBudget_nonpos
#check not_forall_upper_tri_det_ne_zero_kappaInf_bound_implies_two_mul_budget_expr_mul_sq_lt_one
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_diagDominant_leadingBlock_det_ne_zero_concreteDualBudget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_diagDominant_leadingBlock_det_ne_zero_concreteDualProductBudget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_diagDominant_leadingBlock_det_ne_zero_concreteDualProductSequenceBudget
#check diagDominanceCounterexample2_det_ne_zero
#check not_forall_upper_tri_diag_nonzero_implies_diagDominant
#check not_forall_upper_tri_det_ne_zero_implies_diagDominant
#check exists_upper_tri_det_ne_zero_kappaInf_bound_not_diagDominant
#check not_forall_upper_tri_det_ne_zero_kappaInf_bound_implies_diagDominant
#check exists_orthogonal_upper_factorization_not_diagDominant
#check not_forall_orthogonal_upper_factorization_implies_diagDominant
#check exactHouseholderQRDiagDominanceCounterexample_step
#check exactHouseholderQRDiagDominanceCounterexample_alpha_sq
#check exactHouseholderQRDiagDominanceCounterexample_den_ne_zero
#check exactHouseholderQRDiagDominanceCounterexampleFP
#check exactHouseholderQRDiagDominanceCounterexample_stored_step
#check exactHouseholderQRDiagDominanceCounterexample_signed_alpha_def
#check exactHouseholderQRDiagDominanceCounterexample_not_diagDominant
#check not_forall_exact_trailing_householder_sequence_implies_diagDominant
#check not_forall_exact_trailing_householder_sequence_implies_diagDominant_and_property
#check not_forall_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_implies_diagDominant
#check exactHouseholderQRDiagDominanceCounterexample_not_activeMaxPivotChoice
#check not_forall_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_implies_activeMaxPivotChoice
#check isInverse_nonsingInv_of_det_ne_zero
#check exists_isInverse_of_det_ne_zero
#check triInv_infNorm_upperBound
#check triInv_infNorm_sq_budget_of_diagDominantUpper
#check triInv_infNorm_sq_budget_of_diagDominantUpper_det_ne_zero
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_diagDominant_leadingBlock_invNorm_budget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_diagDominant_leadingBlock_det_ne_zero_invNorm_budget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_leading_block_det_ne_zero_sqrt_budget
#check LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_triangular_leading_blocks_sqrt_budget
#check HouseholderAppError
#check HouseholderAppError.of_forward_error
#check fl_householderApplyExplicit
#check fl_householderApplyExplicitPanel
#check fl_householderApplyExplicit_forward_error_bound
#check fl_householderApplyExplicit_HouseholderAppError
#check fl_householderApplyExplicitPanel_HouseholderColumnwisePanelAppError
#check householderDot
#check householderAbsDotBudget
#check fl_householderApplyCompact
#check fl_householderApplyCompactPanel
#check householderCompactComponentBudget
#check householderCompactComponentBudget_nonneg
#check matMulVec_householder_eq_compact
#check fl_householderApplyCompact_componentwise_error_bound
#check fl_householderApplyCompact_forward_error_bound
#check fl_householderApplyCompact_HouseholderAppError_of_budget
#check fl_householderApplyCompactPanel_HouseholderColumnwisePanelAppError_of_budget
#check fl_householderStoredRhsStep_componentwise_error_bound
#check fl_householderStoredRhsStep_forward_error_bound
#check fl_householderStoredPanelStep_column_componentwise_error_bound
#check fl_householderStoredPanelStep_column_forward_error_bound
#check fl_householderStoredPanelStep_HouseholderColumnwisePanelAppError_of_budget
#check frobNormSqRect_eq_sum_vecNorm2Sq_cols
#check frobNormRect_le_of_col_vecNorm2_le
#check HouseholderPanelAppError
#check householderPanelAppError_rect_orthogonal_matrix_vector_sequence_geometric
#check HouseholderColumnwisePanelAppError
#check HouseholderColumnwisePanelAppError.of_vector_applications
#check HouseholderColumnwisePanelAppError.of_forward_errors
#check orthogonal_vector_sequence_one_step_fixedQ
#check rect_orthogonal_columnwise_vector_sequence_geometric
#check fl_householderApplyCompactPanel_rect_orthogonal_columnwise_vector_sequence_geometric
#check householderColumnwisePanelAppError_rect_orthogonal_columnwise_vector_sequence_geometric
#check LSQRSolveBackwardError.of_compact_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget
#check RectLSNormalEquations.of_orthogonal_left
#check storedQRFinalR
#check storedQRFinalTopRhs
#check storedQRBackSubSolution
#check lsQRSolveBackwardSolverDx
#check lsQRSolveBackwardSolverDx_nonneg
#check gram_forward_error_certificate_of_ls_qr_solve_backward_error
#check normalEqCholeskyXHat
#check normalEqCholeskyGramBound
#check normalEqCholeskyRhsBound
#check normalEqCholeskySolverDx
#check normalEqCholeskySolverDx_nonneg
#check normal_equations_cholesky_forward_error_certificate
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_forward_error
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_perturbed_gram_solver
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_ls_qr_backward_error_solver
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_offDiagonalControl_solver
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_offDiagonalControl_solver_of_diagDominant_finiteMaxSmallness
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_sourceOffDiagonalControl_solver
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_leadingBlock_det_ne_zero_normSqBudget_offdiag_product_solver
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_solver
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_kappaInf_dualBudget_solver
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_globalProduct_kappaInf_dualBudget_solver
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowMaxDiagDefect_globalProduct_solver
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowMaxDiagDefect_globalProduct_solver_of_actualUnitRoundoff_no_gammaValid
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_globalProduct_activeMaxPivot_kappaInf_dualBudget_solver
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_solver
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_solver_of_horizonBudget
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_kappaInf_dualBudget_solver
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_kappaInf_dualBudget_solver_of_horizonBudget
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_kappaInf_dualBudget_solver
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_kappaInf_dualBudget_solver_of_horizonBudget
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver_of_horizonBudget
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver_of_actualUnitRoundoff_no_gammaValid
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver_of_actualUnitRoundoff_no_gammaValid_of_horizonBudget
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver_of_horizonBudget
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver_of_actualUnitRoundoff_no_gammaValid
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver_of_actualUnitRoundoff_no_gammaValid_of_horizonBudget
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSmallness_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSmallness_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_concreteDual_solver
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver_of_horizonBudget
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver_of_actualUnitRoundoff_no_gammaValid
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver_of_actualUnitRoundoff_no_gammaValid_of_horizonBudget
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver_of_actualUnitRoundoff_no_gammaValid_of_horizonBudget
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_globalProduct_kappaInf_dualBudget_solver
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSmallness_kappaInf_dualBudget_solver
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSmallness_concreteDual_solver
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSmallness_concreteDual_solver_of_diagDominant
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSourceDenURationalGammaCanonicalBounds_solver
#check leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_normal_eq_cholesky_solver
#check residualCoordinates
#check ResidualsInColumnSpace
#check ColumnsAndRhsInColumnSpace
#check residualCoordinatesFromColumns
#check residualsInColumnSpace_of_residual_representation
#check lsResidual_eq_basis_sum_of_columnsAndRhsInColumnSpace
#check residualsInColumnSpace_of_columnsAndRhsInColumnSpace
#check euclideanVec
#check augmentedDataVector
#check augmentedDataSpan
#check augmentedSpanBasisMatrix
#check augmentedSpanColumnCoords
#check augmentedSpanRhsCoords
#check hasOrthonormalColumns_augmentedSpanBasisMatrix
#check columnsAndRhsInColumnSpace_augmentedSpanBasisMatrix
#check residualsInColumnSpace_augmentedSpanBasisMatrix
#check hasOrthonormalColumns_idMatrix
#check residualCoordinates_idMatrix
#check residualsInColumnSpace_idMatrix
#check lsObjective_eq_vecNorm2Sq_residualCoordinates_of_residualsInColumnSpace
#check rowSampleLSResidualWithBasisScale_eq_coord
#check rowSampleLSObjectiveWithBasisScale_eq_coordinate_quadratic_error
#check preservesLSObjective_of_coordinate_quadratic_error
#check eventProb_preservesLSObjective_of_coordinate_quadratic_error
#check preservesLSObjective_of_coordinate_finiteLoewner_error
#check eventProb_preservesLSObjective_of_coordinate_finiteLoewner_error
#check lsObjective_le_of_sketch_preserves
#check lsObjective_le_one_add_eta_of_sketch_preserves
#check eventProb_lsObjective_le_of_preserves
#check eventProb_lsObjective_le_one_add_eta_of_preserves
#check eventProb_lsObjective_le_one_add_eta_of_coordinate_quadratic_error
#check eventProb_lsObjective_le_one_add_eta_of_coordinate_finiteLoewner_error
#check leverageTraceProbability_eventProb_lsObjective_le_one_add_eta_of_coordinate_quadratic_error
#check leverageTraceProbability_eventProb_rowSampleLSObjective_le_one_add_eta_of_residual_coordinates
#check leverageTraceProbability_eventProb_rowSampleLSObjective_le_one_add_eta_of_residualsInColumnSpace
#check leverageTraceProbability_eventProb_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan
#check leverageTraceProbability_eventProb_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget
#check leverageTraceProbability_eventProb_rowSampleLSObjective_le_one_add_eta_of_idBasis
#check leverageTraceProbability_eventProb_fl_lsObjective_le_one_add_eta_of_coordinate_quadratic_error
#check leverageTraceProbability_eventProb_fl_lsObjective_le_one_add_eta_of_augmentedSpan
#check leverageTraceProbability_eventProb_fl_lsObjective_le_one_add_eta_of_augmentedSpan_sample_budget
#check leverageTraceProbability_eventProb_fl_lsObjective_le_one_add_eta_of_idBasis
```

## Module structure

```
LeanFpAnalysis/FP/
├── Model.lean                  — Axiomatic FPModel
├── Analysis/
│   ├── Error.lean              — Error measures (§1.2)
│   ├── Rounding.lean           — γ-function, product error bounds (§3.1, §3.4)
│   ├── Summation.lean          — Summation error (§3.1)
│   ├── SubtractionFold.lean    — Subtraction fold error (§3.1)
│   ├── Stability.lean          — Backward stability definitions (§1.7–1.9)
│   ├── ForwardError.lean       — Forward error from backward error (§8.2)
│   ├── FiniteProbability.lean  — Finite probability, Markov/Chebyshev/Chernoff kernels
│   ├── FirstOrderFramework.lean — First-order staged Jacobian error framework
│   ├── MatrixAlgebra.lean      — Exact matrix algebra, norms, and rectangular orthogonal invariance
│   ├── MatrixSpectral.lean     — Hermitian spectral and matrix-exponential bridges
│   ├── CStarMatrixBridge.lean  — finite real matrix embeddings into complex C⋆-matrices
│   ├── CStarMatrixTrace.lean   — trace bridge for embedded complex C⋆-matrices
│   ├── CStarMatrixExpectation.lean — finite expectations/order/Jensen for complex C⋆-matrix random variables
│   ├── OperatorLog.lean        — operator-log/exponential bridge for future trace-MGF work
│   ├── LiebTrace.lean          — Lieb, relative entropy, and one-step trace-MGF foundations
│   ├── MatrixConcentration.lean — trace-exponential/eigenvalue probability bridge and scalar Bennett budgets
│   └── PerturbationTheory.lean — Forward-error perturbation theory
└── Algorithms/
    ├── DotProduct.lean         — Dot product (§3.1)
    ├── BlockDotProduct.lean    — Equal-block dot-product route (§3.1)
    ├── ExtendedPrecisionDotProduct.lean — Extended-precision dot products (§3.1)
    ├── MatVec.lean             — Matrix-vector product (§3.5)
    ├── OuterProduct.lean       — Outer product (§3.1)
    ├── MatMul.lean             — Matrix multiplication
    ├── RandNLA/
    │   ├── ElementwiseSampling.lean    — Algorithm 1 updates, traces, hit counts, stability events
    │   ├── HitCountConcentration.lean  — Markov, Chebyshev, Chernoff high-probability stability
    │   ├── ElementwiseTraceMGF.lean    — Algorithm 1 trace-MGF product-law and iid-sum adapters
    │   ├── ElementwiseSpectral.lean    — Algorithm 1 equation (2) FP spectral-transfer layer
    │   ├── RowSampling.lean            — Algorithm 2 row probabilities, traces, and sampled sketches
    │   ├── RowSamplingGram.lean        — Algorithm 2 Gram expectation, equation (5), and FP perturbation
    │   ├── RowSamplingLeverage.lean    — Algorithm 2 equation (6)/(7) leverage-score specialization
    │   ├── RowSamplingTraceMGF.lean    — Algorithm 2 trace-MGF product-law adapters
    │   ├── RowSamplingLeverageMGF.lean — Algorithm 2 leverage log-CGF, Bennett sample budget, and FP Loewner transfer
    │   ├── UniformRowSampling.lean     — uniform row outer-product foundations for Algorithm 3
    │   ├── UniformRowSamplingMGF.lean  — uniform row trace-MGF and concentration route for Algorithm 3
    │   ├── UniformRowSamplingComposition.lean — product-law Algorithm 3 preprocessing/sampling composition
    │   ├── UniformRowSamplingFP.lean   — floating-point uniform sketch/Gram transfer for Algorithm 3
    │   ├── Preconditioning.lean        — Algorithm 3 random-projection preprocessing stability
    │   ├── LeastSquaresSketch.lean     — Equation (8) deterministic sketched-LS objective guarantee
    │   └── LowRankApprox.lean          — Equation (9) low-rank rank-factorization vocabulary
    ├── RecursiveSum.lean       — Recursive and higher-precision recursive summation (§4.1–4.2, §4.6)
    ├── InsertionSum.lean       — Displayed insertion examples (§4.1–4.2)
    ├── OrderingExamples.lean   — Recursive ordering/cancellation example (§4.2)
    ├── CompensatedSum.lean     — Correction formula, Kahan, alternative, and no-guard traces (§4.3)
    ├── DoublyCompensatedSum.lean — Priest doubly compensated summation trace (§4.4)
    ├── PairwiseSum.lean        — Pairwise summation (§4.2)
    ├── SumTree.lean            — Tree summation (§4.2)
    ├── TriangularSolve.lean    — Back substitution (§8.1)
    ├── ForwardSub.lean         — Forward substitution (§8.1)
    ├── TriangularSolveCombined.lean    — Combined LU solve (§8.1)
    ├── TriangularForwardBound.lean     — Diagonal dominance bounds (§8.2)
    ├── TriangularForwardComparison.lean — Comparison matrix bounds (§8.2)
    ├── InverseBounds.lean      — Inverse bounds (§8.3)
    ├── MMatrix.lean            — M-matrix properties (§8.2)
    └── LU/
        ├── GaussianElimination.lean    — LU backward error (§9.3)
        ├── LUSolve.lean                — LU solve backward error (§9.4)
        ├── GrowthFactor.lean           — Growth factor (§9.3–9.4)
        ├── SpecialMatrices.lean        — SPD, M-matrix, sign-equivalent (§9.4)
        ├── Tridiagonal.lean            — Banded/tridiagonal LU (§9.5)
        ├── TridiagonalRecurrence.lean  — Tridiagonal recurrence
        └── Doolittle.lean              — Doolittle algorithm
```

## Roadmap

More chapters from Higham are planned. Contributions and requests are welcome — open an issue if there's a specific algorithm or result you need formalized.

## References

N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM, 2002.

P. Drineas and M. W. Mahoney, ["RandNLA: Randomized Numerical Linear Algebra"](https://dl.acm.org/doi/10.1145/2842602), *Communications of the ACM*, 59(6), 80-90, 2016.

## License

MIT
