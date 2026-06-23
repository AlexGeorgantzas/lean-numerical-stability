# Split 1 Chapter 1 Core Audit

Date: 2026-06-18

Skill: `chapter_splitting/skills/higham_chapter_formalization_shared_SKILL.md`

Planning documents used, in required order: `HIGHAM_PARALLEL_FORMALIZATION_BLUEPRINT.md`, Split 1 section of `split_primary_contracts.md`, and `chapter_index.md`.

Source PDFs:

- `References/1.9780898718027.ch1.pdf`
- `References/1.9780898718027.appa.pdf`

Scope: Split 1, Chapter 1, core mode.  The chapter PDF metadata identifies the SIAM e-book chapter by title and DOI-style filename.  The standalone chapter PDF does not include a title/copyright page that separately prints the edition, but the numbering, section titles, and problem/appendix labels match the supplied split contracts.

Baseline: `lake build` completed successfully before this audit.  A placeholder scan over `LeanFpAnalysis`, `Main.lean`, and `examples` found no `sorry`, `admit`, top-level `axiom`, or `opaque`.

## Core Result Inventory

| Source item | Classification | Lean status |
|---|---|---|
| Lemma 1.1, relative residual as optimal relative matrix-only backward error in the 2-norm | Core named result | Closed by `higham_lemma_1_1_operator2_predicate`, `higham_lemma_1_1_relativeResidual2_predicate`, and `relativeResidual2_le_of_relativeMatrixOnlyBackwardError2Le` in `LeanFpAnalysis/FP/Analysis/PerturbationTheory.lean`. |
| Equation (1.1), standard model for a basic operation | Core model equation, with Chapter 2 dependency | Closed by `BasicOp`, `FPModel.model_basicOp`, `signedRelErrorWitness`, and the finite-format Chapter 2 wrappers in `FloatingPointArithmetic.lean`. |
| Equation (1.2), mixed forward-backward error | Core definition | Closed by `mixedForwardBackwardErrorBounded`, `mixedForwardBackwardErrorBoundedVec`, and `isNumericallyStable` in `Stability.lean`. |
| Equation (1.3), quadratic formula and cancellation/recovery discussion | Core exact algebra plus selected roundoff analysis | Closed by `quadraticRootPlus_is_root`, `quadraticRootMinus_is_root`, `quadratic_roots_product`, `quadraticRootMinus_eq_c_div_a_mul_rootPlus`, `quadraticRootSmallByBSign_abs_le_largeByBSign`, and the rounded-discriminant/root error surfaces in `Quadratic.lean`. |
| Equations (1.4) and (1.5), two-pass and one-pass sample variance | Core exact identities | Closed by `sampleVarianceTwoPass`, `sampleVarianceOnePass`, `sum_sq_sub_sampleMean_eq`, `sampleVarianceTwoPass_eq_onePass`, and shifted one-pass variants in `SampleVariance.lean`. |
| Equations (1.6a) and (1.6b), updating formulae for `M_k` and `Q_k` | Core exact recurrence plus rounded update analysis | Closed by `prefixMean_succ`, `prefixCorrectedSumSquares_succ`, `flPrefixMeanStep_eq_exact_with_local_errors`, `flPrefixCorrectedSumSquaresStep_eq_exact_with_local_errors`, and `flSampleVarianceUpdate_abs_error_le_budget` in `SampleVariance.lean`. |
| Equation (1.7), residual lower bound in Lemma 1.1 proof | Core proof step | Closed inside the two Lemma 1.1 predicate theorems in `PerturbationTheory.lean`. |
| Equation (1.8), fixed `x + a sin(bx)` precision example | Fixed numerical example plus empirical plot | Exact machine-independent substrate closed by `increasingPrecisionSinExampleSource_perturbation_abs_le` and related finite round-to-even facts in `IncreasingPrecision.lean`; Figure 1.4's plotted output is empirical-source-output and not a theorem gate. |
| Equation (1.9), Algorithm 2 rounded core for `(exp x - 1)/x` | Core symbolic roundoff equation | Closed by `expm1Algorithm2RoundedCore_eq_source_1_9`, `expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma4`, and local error bounds in `CancellationOfRoundingErrors.lean`. |

## Problem And Appendix Rows

| Source item | Classification | Lean status |
|---|---|---|
| Problem 1.1 / Appendix A 1.1, exact- and computed-denominator relative-error inequalities | Core exercise | Closed by `problem_1_1_relError_bounds` and its component inequalities in `Error.lean`. |
| Problem 1.2 / Appendix A 1.2, near-integer table ambiguity | Core logical claim plus fixed table data | Closed by `problem12TableConsistent`, `problem_1_2_candidateBelow_consistent`, `problem_1_2_candidateInteger_consistent`, and `problem_1_2_table_does_not_force_last_digit_four` in `NearInteger.lean`.  The printed decimal table is recorded as fixed source data, not a routine-output proof. |
| Problem 1.3 / Appendix A 1.3, five cancellation-avoiding rewrites | Core exercise | Closed by `problem_1_3_sqrt_one_add_sub_one`, `problem_1_3_sin_sub_sin`, `problem_1_3_sq_sub_sq`, `problem_1_3_one_sub_cos_div_sin`, and `problem_1_3_lawOfCosines_sqrt_halfAngle` in `TrigCancellation.lean`. |
| Problem 1.4 / Appendix A 1.4, stable complex square-root formulae | Core exercise | Closed by `complexSqrtStable_nonnegA_sq`, `complexSqrtStable_negA_sq`, and `complexSqrtStable_zero_sq` in `ComplexSqrt.lean`. |
| Problem 1.5 / Appendix A 1.5, compensated `log(1+x)` and `exp(n log(1+1/n))` | Core symbolic exercise; concrete routine behavior remains model-specific | Closed by new `logOnePlusCompensatedExact`, `logOnePlusCompensatedExact_eq_log_one_add`, `logOnePlusCompensatedPerturbedNonbranch_exact_w_*` declarations in `Accumulation.lean`, plus existing `expOneApproxLogExpExact_eq_exact_base`, `expOneApproxLogExp_logRelError_exponent_abs_le`, and `expOneApproxLogExpRoundedOuter_relError_le_fp`. |
| Problem 1.6 / Appendix A, pocket-calculator upside-down words | Recreational machine/display exercise | Not a core theorem gate.  Existing optional exact glyph formalization is `CalculatorGlyph`, `calculatorInvertDigits`, and `problem_1_6_*` in `CalculatorWords.lean`. |
| Problem 1.7 / Appendix A 1.7, sample-variance condition numbers | Core exercise | Closed by `sampleVarianceTwoPass_add_scaled_sub_eq`, `sampleVarianceDirectionalCoeff_componentwise_le`, `sampleVarianceDirectionalCoeff_normwise_le`, `sampleVarianceKappaNClosed_eq_expanded`, and `sampleVarianceKappaCClosed_le_KappaNClosed` in `SampleVariance.lean`. |
| Problem 1.8 / Appendix A 1.8, Muller recurrence | Mixed: exact recurrence theorem plus empirical instruction to implement | Exact/theoretical subclaims closed by `mullerExact_satisfies_recurrence`, `mullerExact_lt_succ`, `mullerExact_tendsto_six`, `problem_1_8_x34_rounds_to_5_998`, `mullerDecimal4Trace_34_eq_100`, and `mullerModeRatio_gt_99_of_dominant`.  "Implement on your computer" is empirical-source-output and not a core gate. |
| Problem 1.9 / Appendix A 1.9, 2-by-2 Cramer's rule bounds | Core exercise | Closed by `cramer2x2Solution_solves`, `flDet2x2_error_le_gamma3`, `cramer2x2Solution_error_from_flNumerators_exact_den`, `cramer2x2Solution_relative_forward_error_from_flNumerators_exact_den_condAt`, `cramer2x2Residual_infNorm_from_flNumerators_exact_den_condInv`, and `gepp2_relativeResidual2_le_wilkinson`. |
| Problem 1.10 / Appendix A 1.10, two-pass sample variance error bound | Core exercise | Closed by `flSampleMean_backward_error`, `flSampleVarianceTwoPassWithMean_eq_mul_one_add_gamma`, `flSampleVarianceTwoPass_relError_le_gamma_add_mean_quadratic`, `gamma_eq_linear_plus_quadratic_remainder`, and `flSampleVarianceTwoPass_relError_le_linear_u_add_explicit_remainder` in `SampleVariance.lean`. |

## Algorithm And Example Classification

| Source location | Claim/output | Classification | Status |
|---|---|---|---|
| Section 1.1 machine environment paragraph | MATLAB/Pentium/Windows details and unit roundoff of experiments | Empirical/machine-specific context | Visible in inventory; skipped as a formal theorem.  Abstract FP model facts are formalized instead. |
| Table 1.1, finite-`n` approximation to `e` | Printed values and relative-error column | Fixed source table plus hidden Fortran/power routine output | Exact rational table rows are recorded in `Accumulation.lean`; hidden routine replay is skipped. |
| Section 1.10.1 GEPP versus Cramer's rule plots/tables | Method comparison outputs | Benchmark/empirical output | Core theorem work is the Cramer and GEPP residual/error surfaces; plotted outputs are not gates. |
| Section 1.13 and Figure 1.4 | Precision plateau for a fixed computation | Fixed computation plus empirical plot | Exact and finite-rounding subclaims are formalized in `IncreasingPrecision.lean`; plotted curve is skipped as empirical output. |
| Table 1.2 | MATLAB values for Algorithms 1 and 2 | Empirical routine output plus fixed displayed decimals | Exact rational transcription and symbolic Algorithm 2 analysis are formalized; MATLAB routine replay is skipped. |
| Section 1.14.2 QR example | Educational foreshadowing of later QR stability | Later-chapter dependency/benchmark-style handoff | Current chapter keeps the Givens block and conditional Stewart handoff visible; full QR stability belongs to the later chapter route. |
| Sections 1.15-1.17 | Beneficial/nonrandom rounding examples and printed outputs | Mixed: exact mechanisms plus empirical printouts | Exact symbolic mechanisms are formalized in `BeneficialRounding.lean` and `NonrandomRounding.lean`; historical machine outputs remain non-gating unless fully specified. |

## Open Ledger

Selected Chapter 1 core rows open after this pass: none found.

Non-core or model-specific strengthenings deliberately not counted as Chapter 1 core gates:

- Replaying MATLAB/Fortran/calculator outputs from the source tables and figures.
- A full concrete implementation contract for every elementary `exp`, `log`, and display routine used in the examples.
- Full QR stability analysis beyond the Chapter 1 illustrative handoff; this belongs to later QR chapters and the Stewart route.
- Historical printed values whose hardware, compiler, library, display, or extended-register semantics are underspecified.

## Validation

- `lake env lean LeanFpAnalysis/FP/Analysis/Accumulation.lean`: passed after adding the Problem 1.5 compensated logarithm declarations.
- `lake build`: passed after the patch.  The build replayed pre-existing QR/FastMatMul linter warnings outside this edit.
- `git diff --check`: passed.
- Placeholder scan: no `sorry`, `admit`, top-level `axiom`, or `opaque` in project Lean/example files.
