# Higham Chapter 1 Source Coverage Ledger

## Source and Scope

- Source: N. J. Higham, *Accuracy and Stability of Numerical Algorithms*,
  2nd ed., Chapter 1, "Principles of Finite Precision Computation".
- Printed pages 1-33.
- Mode: core.
- Ownership: foundational/shared. Chapter 1 supplies the repository-wide
  model and vocabulary (`Model.lean`, `Error.lean`, `Stability.lean`); its
  declarations are consumed by every later chapter's split rather than owned
  by a single split lane.
- Core primary labels: Lemma 1.1 (the only numbered theorem-level result in
  the chapter).
- Core numbered equations: (1.1)-(1.9), including (1.6a)/(1.6b).
- Problems audited: 1.1-1.7, 1.9, 1.10 (task scope); 1.8 recorded as a bonus
  row. Problems are OPTIONAL in core mode; their status is recorded without
  treating absence as gate failure.
- Chapter character: Chapter 1 is largely motivational prose around a small
  set of precise claims (the standard model (1.1), the backward/forward
  error, stability and conditioning definitions, Lemma 1.1, and the worked
  cancellation/variance/quadratic analyses). Editorial passages are
  classified SKIP-OK below with reason codes.
- Canonical source entry point: `NumStability.Source.Higham.Chapter01`.
  Section 1.17 is the complete
  `NumStability.Source.Higham.Chapter01.Section17` family, split into the
  `HornerEvaluation`, `SourceInterval`, `GridVariation`, `StoredGrid`, and
  `ErrorSpread` leaves. The former `NumStability.Analysis.NonrandomRounding*`
  paths are compatibility imports only.
- Current aggregate status: **CORE VERIFIED (selected-scope gate PASS)**.

Status language:

- **VERIFIED**: a compiled Lean declaration genuinely formalizes the printed
  row at honest strength (constants derived, no hidden target-equivalent
  hypothesis).
- **PARTIAL**: formalized weaker or conditionally; the exact residual is
  stated.
- **SKIP-OK(reason)**: editorial prose, figures, machine-specific output, or
  empirical tables not selected for formalization.

Axiom spot-check (throwaway `#print axioms`, deleted after use): the six
load-bearing declarations
`higham_lemma_1_1_operator2_predicate`,
`higham_lemma_1_1_relativeResidual2_predicate`,
`flSampleVarianceTwoPass_relError_le_linear_u_add_problem110_remainder`,
`expm1Algorithm2RoundedCore_relError_le_gamma3`,
`forward_from_backward`, and
`cramer2x2Solution_relative_forward_error_from_flNumerators_exact_den_condAt`
all report exactly `[propext, Classical.choice, Quot.sound]`.

## Primary Contracts

| Source label | Printed statement | Status | Lean coverage | Exact scope notes |
| --- | --- | --- | --- | --- |
| Lemma 1.1 (S1.10) | For the 2-norm, the relative residual `rho(y) = \|\|b-Ay\|\|_2/(\|\|A\|\|_2 \|\|y\|\|_2)` equals `min { \|\|dA\|\|_2/\|\|A\|\|_2 : (A+dA)y = b }`, attained by `dA = r y^T/(y^T y)`. | **VERIFIED** | `NumStability/Analysis/PerturbationTheory.lean`: `higham_lemma_1_1_operator2_predicate` (absolute form: `\|\|r\|\|_2/\|\|y\|\|_2` is an admissible operator-2 budget and is a lower bound for every admissible budget), `higham_lemma_1_1_relativeResidual2_predicate` (relative form), with the constructive route `residualRankOnePerturbation`, `residualRankOnePerturbation_solves`, `opNorm2Le_residualRankOnePerturbation`, `frobNorm_residualRankOnePerturbation`, and the lower-bound direction (1.7) `residual_norm_div_solution_norm_le_of_opNorm2Le_perturbed_solve`; direct use form `relativeResidual2_le_of_relativeMatrixOnlyBackwardError2Le`. | Two honest representation choices, both faithful: (i) the operator 2-norm enters through the repository predicate `opNorm2Le M c` (`forall x, \|\|Mx\|\|_2 <= c \|\|x\|\|_2`); the printed `min` over exact norms is captured as the least admissible budget, which is the same number since the exact norm of each `dA` is its least budget. (ii) In the relative form `\|\|A\|\|_2` is an explicit positive scalar parameter `matrixNormA`; because the printed statement divides both sides by the same `\|\|A\|\|_2`, the equality holds verbatim for any positive value, so no strength is lost. Domain hypothesis `\|\|y\|\|_2 /= 0` matches the printed implicit assumption (rho undefined for `y = 0`). |

## Equation Ledger

| Equation | Status | Formalized content |
| --- | --- | --- |
| (1.1) standard model `fl(x op y) = (x op y)(1+delta)`, `\|delta\| <= u` | **VERIFIED** (model definition) | `NumStability/FloatingPoint/Model.lean`: `FPModel` structure fields `model_add/sub/mul/div` (and `model_sqrt`, per Higham's Chapter 2 note), unified form `FPModel.model_basicOp` over the `BasicOp` inductive. Non-strict `\|delta\| <= u` variant of the printed `\|delta\| < u` is documented in the module docstring. `FPModel.not_forall_u_le_cap` records that no numeric cap on `u` follows from the abstract model. Division carries the `y /= 0` side condition. |
| (1.2) mixed forward-backward result `yhat + dy = f(x+dx)`, `\|dy\| <= eps\|y\|`, `\|dx\| <= eta\|x\|` | **VERIFIED** (definition surface) | `NumStability/Analysis/Stability.lean`: `mixedForwardBackwardErrorBounded` / `...Vec`, with `mixedForwardBackward_of_backward`; numerical stability in the sense of (1.2) named by `isNumericallyStable` / `isVectorNumericallyStable`. Note: the Lean predicate takes absolute budgets `epsBack`, `epsForw`; the printed relative form is the instantiation `epsBack = eta*\|x\|`, `epsForw = eps*\|y\|`, so the definition is parametric rather than weaker. |
| (1.3) quadratic formula `x = (-b +- sqrt(b^2-4ac))/(2a)` | **VERIFIED** | `NumStability/Analysis/Quadratic.lean`: `quadraticRootPlus_is_root`, `quadraticRootMinus_is_root` (with `s^2 = b^2-4ac` supplied as the square-root witness), `quadratic_roots_sum`, `quadratic_roots_product`; the S1.8 stability content is also formalized: stable second-root recovery `quadraticRootMinus_eq_c_div_a_mul_rootPlus` (and mirror), sign-based large/small root selection with cancellation-avoidance bounds, rounded-discriminant error bounds (`flQuadraticDiscriminant_abs_error_le`), the nearly-equal-roots obstruction (`quadraticRoots_near_midpoint_of_discriminant_le`), and the "extended precision for `b^2-4ac`" principle (`flQuadraticDiscriminantAbsErrorBound_le_of_simulatesHigherPrecision`). |
| (1.4) two-pass sample variance | **VERIFIED** | `NumStability/Analysis/SampleVariance.lean`: `sampleVarianceTwoPass`, `sampleMean`, nonnegativity `sampleVarianceTwoPass_nonneg`, accuracy under rounding via the Problem 1.10 rows below. |
| (1.5) one-pass textbook formula | **VERIFIED** | `sampleVarianceOnePass`, exact equivalence `sampleVarianceTwoPass_eq_onePass`, and the printed failure mode: `sampleVarianceOnePassAggregates_neg_of_sumSq_lt` (computed value can be negative), plus the full IEEE-single round-to-even trace of the printed `x = [10000,10001,10002]` example: `sampleVarianceOnePassIeeeSingleTrace_zero` and `..._relError_one` (one-pass computes 0.0, relative error 1), with the two-pass exact value 1 (`sampleVarianceTwoPass_example_10000_10001_10002`). |
| (1.6a)/(1.6b) updating formulae `M_k`, `Q_k` | **VERIFIED** (recurrences and rounded trajectories) | `prefixMean`, `prefixCorrectedSumSquares`, exact recurrences `prefixMean_succ`, `prefixCorrectedSumSquares_succ`, `s_n^2 = Q_n/(n-1)` via `sampleVariancePrefix` / `flSampleVarianceUpdate`; rounded one-step and multi-step error budgets `flPrefixMeanTrajectory_abs_error_le_budget`, `flPrefixCorrectedSumSquaresTrajectory_abs_error_le_budget`, `flSampleVarianceUpdate_abs_error_le_budget`; the exact-recovery of the printed numerical example `sampleVarianceUpdate_example_10000_10001_10002`. Residual (non-gating, qualitative sentence): the source's remark that the updating formulae's error bound is "proportional to kappa_N" is represented only by explicit trajectory budgets, not by a kappa_N-shaped closed bound. |
| (1.7) `\|\|dA\|\|_2/\|\|A\|\|_2 >= \|\|r\|\|_2/(\|\|A\|\|_2\|\|y\|\|_2)` (proof step of Lemma 1.1) | **VERIFIED** | `residual_norm_div_solution_norm_le_of_opNorm2Le_perturbed_solve` and `residualVec_eq_matMulVec_of_perturbed_solve` (the identity `r = dA y`). |
| (1.8) `y = x + a sin(bx)`, `x = 1/7`, `a = 10^-8`, `b = 2^24` | **VERIFIED** (instance algebra) / **SKIP-OK(empirical)** for Figure 1.4 | `NumStability/Analysis/IncreasingPrecision.lean`: the source instance and constants are defined; exact IEEE-single/double storage errors for `x = 1/7`, spacing certificates, the dyadic-amplitude threshold behind the early-precision plateau, and the `t`-digit storage-error core `1/(7*2^t)`. The plotted error-versus-precision curve itself is machine output (SKIP-OK). |
| (1.9) `fl((yhat-1)/log yhat) = ((yhat-1)(1+eps1)/(log yhat (1+eps2)))(1+eps3)`, `\|eps_i\| <= u` | **VERIFIED** | `NumStability/Analysis/CancellationOfRoundingErrors.lean`: `expm1Algorithm2RoundedCore_eq_source_1_9` derives the printed form from the `FPModel` laws (the rounded logarithm supplied as `log(yhat)(1+epsLog)` exactly as in the source's assumption that exp/log have relative error at most `u`); guard-digit and Sterbenz exact-subtraction instantiations (`..._of_guardDigitSubtractionModel`, `..._of_finiteRoundToEven_sterbenz_radius`) close the subtraction factor. |

## Section Prose Obligations

| Row | Status | Notes |
| --- | --- | --- |
| S1.1 notation, flop conventions, MATLAB setup | **SKIP-OK(editorial/notation)** | Notation and experimental-environment prose. The one precise object, (1.1), is verified above. |
| S1.2 absolute/relative error definitions; `Erel = \|rho\|` with `xhat = x(1+rho)`; scale independence; componentwise relative error | **VERIFIED** | `NumStability/Analysis/Error.lean`: `absError`, `relError`, `relErrorDefined`, `signedRelErrorWitness`, `relError_eq_abs_of_signedRelErrorWitness`, converse `exists_signedRelErrorWitness_of_relErrorDefined`, scale independence `relError_smul` (and `absError_smul`), normwise `normwiseRelError`, componentwise `compRelError` with `compRelError_le_iff`. |
| S1.2 correct-significant-digits discussion (0.9949/0.9951 anomaly, 0.123/0.127, tablemaker's dilemma) | **SKIP-OK(definitional digression)** | The source introduces these decimal-rounding definitions only to argue they are problematic and to prefer relative error, which is the surface actually used downstream and is fully formalized. No Lean encoding of decimal significant-digit counting exists; recorded honestly as unformalized non-gating prose. |
| S1.3 sources of errors taxonomy | **VERIFIED** (taxonomy) / **SKIP-OK(editorial)** for the discussion | `ErrorSource` inductive with `chapterOneMainSource_exhaustive`. The Trefethen quotation and truncation-error discussion are editorial. |
| S1.4 precision versus accuracy; "accuracy is not limited by precision" | **VERIFIED** (definitional surface) | `AccuracyMeasure`, `PrecisionMeasure`, `PrecisionMeasure.ofFPModel`, `BasicOperationPrecisionBounded` with `FPModel.basicOperationPrecisionBounded`, and the simulation caveat named by `SimulatesHigherPrecision` (used concretely by the quadratic-discriminant row above). The Priest-style formal proof that precision does not limit accuracy is out of scope (source itself defers to S27.9 / Priest). |
| S1.5 backward/forward error, backward stable, mixed stability, numerically stable | **VERIFIED** | `Stability.lean`: `backwardErrorBounded(Vec)`, `forwardErrorBounded(Vec)`, `normwiseBackwardErrorBoundedVec`, `mixedForwardBackwardErrorBounded(Vec)`, `isBackwardStable`, `isVectorBackwardStable`, `isNumericallyStable`, `isForwardStableRelativeTo`. The remark that (1.1) makes `x +- y` backward stable is immediate from `FPModel.model_add/sub` plus the S1.7 algebra (`subtract_perturbed_error_eq`). |
| S1.6 condition number `c(x) = \|x f'(x)/f(x)\|`; rule of thumb `forward error <~ condition number x backward error`; forward stability | **VERIFIED** (with documented conditional form) | `condNumber`, `isWellConditioned`, vector surfaces `normwiseConditionNumberBoundedVec` / `...SupremumVec` / `...AttainedVec`; scalar rule of thumb `forward_from_backward`; normwise rule of thumb `normwise_forward_from_backward_vec(_of_condition_supremum)`. Honest note: the scalar theorem carries an explicit linearisation hypothesis `\|f(a+da)-f(a)\| <= \|df(a)\|\|da\|` in place of the source's twice-differentiable Taylor argument; since the printed rule of thumb is itself a first-order heuristic (`<~`), this conditional form is the honest formal counterpart, and the residual is documented here. The `log x` illustration is SKIP-OK(illustrative). |
| S1.7 cancellation: `(x-xhat)/x = (-a da + b db)/(a-b)` and the `max(\|da\|,\|db\|)(\|a\|+\|b\|)/\|a-b\|` bound | **VERIFIED** | `Error.lean`: `subtract_perturbed_error_eq`, `abs_subtract_perturbed_error_le(_eps)`, `relError_subtract_perturbed_le_eps_amp`; the `(1-cos x)/x^2` example with the `sin(x/2)` rewrite and the displayed ten-figure values in `NumStability/Analysis/TrigCancellation.lean` (including the range fact `0 <= f(x) < 1/2`). |
| S1.8 quadratic equation discussion | **VERIFIED** for the analytic claims (see (1.3) row) / **SKIP-OK(machine-specific)** for the IEEE-single overflow anecdote (`10^20 x^2 - 3.10^20 x + ...`) | Scaling-strategy details are Notes-and-References material in the source itself. |
| S1.9 sample variance discussion | **VERIFIED** | See (1.4)-(1.6) rows; both the accuracy contrast and the printed numerical example are formalized to the IEEE bit level. |
| S1.10 residual, relative residual, backward-error interpretation | **VERIFIED** | `residualVec`, `relativeResidual2`, `matrixOnlyBackwardError2Le`, `relativeMatrixOnlyBackwardError2Le`, and Lemma 1.1 above. |
| S1.10.1 GEPP versus Cramer's rule | **VERIFIED** (displayed data and analytic anchors) | `NumStability/Analysis/CramersRule.lean`: exact 2x2 Cramer algebra (`cramer2x2Solution_solves`), the printed MATLAB table encoded exactly (`cramerGeppExample_*` rows, residual/scaled-residual gaps, inf-norm and 2-norm-squared comparisons), the `[1.0006, 2.0012]` more-accurate-but-larger-residual comparison vector; the rounded-exact-solution argument `z = fl(x)` giving `\|\|b-Az\|\|_2 <= u\|\|A\|\|_2\|\|x\|\|_2` in `PerturbationTheory.lean` (`roundedExactSolution_residual_norm_le_opNorm2_mul_relative_error`, `roundedExactSolution_relativeResidual2_le_relative_error_factor`). The general GEPP residual guarantee is a S9.3 pointer (Chapter 9 scope). Forward stability of Cramer for `n = 2` is the Problem 1.9 row. |
| S1.11 accumulation of rounding errors; Table 1.1; Strassen remark | **VERIFIED** (exact anchors) / **SKIP-OK(empirical)** for the measured values as such | `NumStability/Analysis/Accumulation.lean`: Table 1.1 rows encoded exactly (`expOneApproxTable11_*`), the single-rounding explanation anchored by `one_div_ten_pow_succ_not_binaryTerminating` (nonterminating binary expansion of `1/10^k`), tail monotonicity of the displayed relative errors; Strassen threshold operation-count facts (`strassenThresholdHalving_same_dimension_and_decreases_count`), with the error-growth direction deferred to S23.2.2 (Chapter 23 scope). |
| S1.12.1 need for pivoting | **VERIFIED** | `NumStability/Analysis/InstabilityWithoutCancellation.lean`: the 2x2 matrix, the exact reproduction error `A - LhatUhat = e2 e2^T`, the conditioning formula `kappa_inf(A) = 4/(1+eps)` (norm value 2 for `0 <= eps <= 1`), the concrete `eps = 2^-24` single-precision instance, and the exact stable pivoted branch. |
| S1.12.2 HP 48G repeated sqrt/square | **VERIFIED** (derivation under abstract calculator laws) | Step surrogate `fhat(x) = 0 for x<1, 1 for x>=1` derived from abstract 12-digit HP 48G laws; two-phase machine trace reproduces the displayed step function. |
| S1.12.3 infinite sum `sum k^-2` | **VERIFIED** (plateau analysis) | The `k = 4096` cutoff (`4096^-2 = 2^-24` drop-off), pre-plateau block bounds, and the printed single-precision plateau value encoded exactly. |
| S1.13 increasing the precision; f(2/3) branch example | **VERIFIED** (examples) / **SKIP-OK(empirical)** Figure 1.3 | See (1.8) row; the contrived `z = f(2/3)` example is formalized including the stored-input branch analysis (`IncreasingPrecision.lean` branch-variable positivity and finite round-to-even storage instances). The Hilbert/Pascal experiment is machine output. |
| S1.14.1 `(e^x-1)/x`: Algorithms 1 and 2, Table 1.2, the ~3.5u claim | **VERIFIED** | `CancellationOfRoundingErrors.lean`: exact equivalence of the two algorithms (`expm1Algorithm2Exact_eq_algorithm1Exact`), Table 1.2 and the page-23 displayed ratios encoded exactly, the `yhat = 1` branch analysis (`expm1Algorithm2_yhat_eq_one_implies_x_eq_neg_log_one_add_delta`), the slow-ratio expansion `g(yhat) - f(x) ~ delta/2` (`expm1LogRatio_*` family), equation (1.9) above, and the printed leading constant: `expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_u_radius_bound_of_unit_bounds` proves relative error `<= (7/2)u + explicit O(u^2) tail`, exactly the honest form of "at most about 3.5u". Gamma-calculus fallbacks (`..._le_gamma3/gamma4`) are labeled as coarser wrappers in their docstrings. |
| S1.14.2 Givens QR cancellation example (Figure 1.5) | **SKIP-OK(empirical example; cross-chapter anchors)** | The precise anchors are Theorem 19.10 (backward stability of Givens QR) and (19.35a) (QR perturbation), which belong to Chapter 19's ledger (`higham_ch19.md`). The specially constructed 10x6 matrix experiment is machine output. |
| S1.15 rounding errors can be beneficial (power method, inverse iteration) | **VERIFIED** (mechanism) | `NumStability/Analysis/BeneficialRounding.lean`: `powerMethodStep`/`powerMethodIterate`, `IsRightEigenpair`; the non-representability mechanism proved exactly (`one_fifth/two_thirds/one_seventh_not_binaryTerminating` and their exclusion from IEEE single/double finite systems, plus round-to-even storage values of every entry of the displayed matrix); inverse iteration formalized through the Lemma 1.1 rank-one backward-error certificate (`inverseIterationShiftedRankOneBackwardError_*`). The Parlett/Golub-Van Loan claim that the inverse-iteration error lies along the eigenvector is a citation in the source, not a Chapter 1 obligation. |
| S1.16 stability depends on the problem (Hessenberg determinant vs. solve); Table 1.3 | **VERIFIED** | `NumStability/Analysis/ProblemDependentStability.lean`: the source-shaped rounded diagonal-update identity with the three `(1+eps)` factors, the nearby-matrix construction (diagonal and subdiagonal entries perturbed by exactly the displayed factors), the mixed forward-backward determinant conclusion in the sense of (1.2) (determinant-product bridge with `gamma fp n` relative factor), Table 1.3 encoded exactly, and the `alpha = 10^-7` instance. The MGS least-squares/orthonormal-basis contrast is a S19.8/S20.3 pointer (other chapters' scope). |
| S1.17 rounding errors are not random (Kahan rational function) | **VERIFIED** (error structure) / **SKIP-OK(empirical)** Figure 1.6 | `NumStability/Source/Higham/Chapter01/Section17.lean` is the complete source aggregate. Its `HornerEvaluation.lean` leaf defines `kahanRationalFunction`, the Horner numerator/denominator rounded traces and exact error-evaluation forms (`flKahanRationalFunction_eq_errorEval`), and the continued-fraction reference form; `SourceInterval.lean`, `GridVariation.lean`, `StoredGrid.lean`, and `ErrorSpread.lean` supply the interval, grid, concrete IEEE-double finite round-to-even, and certified spread layers. The plotted 361-point pattern is machine output. |
| S1.18 designing stable algorithms (six guidelines) | **SKIP-OK(advice/editorial)** | Design guidance; the load-bearing instances (GE, summation, MGS, iterative refinement) are other chapters' obligations. |
| S1.19 misconceptions list | **SKIP-OK(editorial summary)** | Each listed misconception is the summary of a section already audited above. |
| S1.20 rounding errors in numerical analysis | **SKIP-OK(editorial survey)** | Literature pointers. |
| S1.21 notes and references | **SKIP-OK(bibliographic)** | Includes the Wilkinson deflation anecdote behind Lemma 1.1 (historical). |

## Problems Accounting (optional in core mode)

| Problem | Status | Lean coverage | Notes |
| --- | --- | --- | --- |
| 1.1 (inequalities between `Erel` and `Etilde_rel`) | **VERIFIED** | `Error.lean`: `problem_1_1_relError_bounds` packaging `relErrorComputedDenom_lower_bound_from_relError`, `..._upper_bound_from_relError`, `relError_lower_bound_from_computedDenom`, `..._upper_bound_from_computedDenom` | Both directions with the sharp `E/(1+-E)` envelopes, under the natural nonzero and `< 1` hypotheses. |
| 1.2 (`e^{pi sqrt 163}` table) | **VERIFIED** | `NearInteger.lean`: one-ulp table predicate, all five displayed rows checked, and the formal answer that the displayed data do not force the last digit before the decimal point | Matches the intended negative answer. |
| 1.3 (five cancellation-avoiding rewrites) | **VERIFIED** | `TrigCancellation.lean`: Problem 1.3(1)-(5) rewrite identities, including both law-of-cosines radicand forms and the square-root form | Exact-algebra identities, which is the content requested. |
| 1.4 (stable complex square root) | **VERIFIED** | `ComplexSqrt.lean`: sign-split stable formulae with `complexSqrtStable_nonnegA_sq`, `complexSqrtStable_negA_sq`, `complexSqrtStable_zero_sq` | The formulae and their correctness (square equals `a+ib`) plus the cancellation-avoiding branch selection; a full rounding-error analysis of the formulae is not claimed by the problem statement. |
| 1.5 (accurate `log(1+x)` and `(1+1/n)^n`) | **VERIFIED** | `Accumulation.lean`: `logOnePlusCompensatedExact` with exact identity `logOnePlusCompensatedExact_eq_log_one_add`, perturbed-branch relative-error theorems, the `exp(n log(1+1/n))` reformulation, and the `O(u)` envelope certificate (`expOneApproxLogExpUnitRoundoffEnvelope_isBigO`) | The Kahan-technique adaptation is formalized at the modeled-rounding level requested by the hint. |
| 1.6 (upside-down calculator words) | **VERIFIED** (recreational) | `CalculatorWords.lean`: digit-to-letter reading with the printed examples | The source itself flags this as recreational. |
| 1.7 (condition numbers `kappa_C`, `kappa_N` of the sample variance) | **PARTIAL** | `SampleVariance.lean`: closed forms `sampleVarianceKappaCClosed`, `sampleVarianceKappaNClosed`, `sampleVarianceKappaNExpanded`; first-order directional coefficient bounded by the closed forms (`sampleVarianceDirectionalCoeff_componentwise_le`, `..._normwise_le`); exact finite-difference expansion with literal `O(eps^2)` Landau remainder; equality of the two printed `kappa_N` displays (`sampleVarianceKappaNClosed_eq_expanded` via `sampleVariance_vecNorm2Sq_eq_conditionDen_add_mean_sq`); the printed inequality `kappa_N >= kappa_C` (`sampleVarianceKappaCClosed_le_KappaNClosed`) | Residual: the printed rows are lim-sup *equalities*; Lean proves the upper-bound direction of the first-order coefficient plus all displayed algebra, but no attainment/supremum theorem showing the closed forms are achieved. This is the one honest open direction in the chapter. |
| 1.8 (Kahan-Muller recurrence) — bonus row, outside task scope | **VERIFIED** | `MullerRecurrence.lean`: exact solution, monotone convergence `x_k -> 6`, four-digit display trace, and a hidden-`100^k`-mode contaminant witness explaining the observed drift to 100 | Recorded for completeness. |
| 1.9 (Cramer's rule forward stable for n = 2) | **VERIFIED** | `CramersRule.lean`: `flDet2x2_error_le_gamma3`, `flCramer2x2Numerator_error_le_gamma3`, forward bound `cramer2x2Solution_relative_forward_error_from_flNumerators_exact_den_condAt` (`<= gamma_3 * cond(A,x)` with `cond(A,x) = \|\| \|A^-1\|\|A\|\|x\| \|\|_inf/\|\|x\|\|_inf`), residual bound `cramer2x2Residual_infNorm_from_flNumerators_exact_den_condInv` (`<= gamma_3 * cond(A^-1) * \|\|b\|\|_inf`) | Formalized under the printed simplifying assumption ("assuming d is computed exactly"), exactly as the problem states it; constants are the printed `gamma_3`. |
| 1.10 (two-pass variance: `\|V - Vhat\|/V <= (n+3)u + O(u^2)`) | **VERIFIED** | `SampleVariance.lean`: `flSampleVarianceTwoPass_relError_le_linear_u_add_problem110_remainder` with the named explicit remainder `flSampleVarianceTwoPassProblem110Remainder`, its explicit quadratic envelope and literal `IsBigO` certificate (`flSampleVarianceTwoPassProblem110RemainderQuadraticEnvelope_isBigO`), non-vacuity at `u = 0` | Printed constant `(n+3)u` recovered exactly; the `O(u^2)` term is an explicit named remainder rather than an unquantified Landau symbol, which is stronger than the printed form. Natural domain hypotheses: `1 < n`, `V(x) > 0`, positive rounded second-pass sum, `gammaValid fp (n+3)`. |

## Honest-Strength Notes

1. Lemma 1.1's `min` is expressed as "least admissible `opNorm2Le` budget";
   this is numerically identical to the printed minimum over exact operator
   norms and avoids committing to a supremum-valued norm definition. The
   relative form takes `\|\|A\|\|_2` as an explicit positive scalar; the printed
   equality is scale-invariant in this parameter, so nothing is weakened.
2. The (1.1) model is the non-strict `\|delta\| <= u` variant (documented in
   `Model.lean`), the repository-wide convention.
3. The S1.6 rule of thumb is proved with an explicit linearisation
   hypothesis standing in for the source's Taylor argument; the source's own
   statement is a first-order heuristic, so this is the honest formal
   counterpart rather than a hidden weakening.
4. The S1.14.1 "about 3.5u" claim is proved as a literal `(7/2)u` leading
   term plus an explicit second-order tail under unit-radius local
   hypotheses that mirror the page-24 setting (`\|y-1\| <= u`,
   `\|yhat-1\| <= u`, `\|delta\| <= u`).
5. Displayed tables (1.1, 1.2, 1.3) and the S1.10.1 MATLAB table are encoded
   as exact rationals with row-by-row equality theorems; figures (1.1-1.6)
   are diagrams or machine output and carry no independent claims beyond
   what is verified above.
6. A docstring citation was never counted as coverage: every VERIFIED row
   above names the theorem whose statement was read and matched against the
   printed claim.

## Selected-Scope Gate

**Selected-scope gate: PASS.**

- Primary label Lemma 1.1: VERIFIED (both directions, attaining perturbation
  constructed, clean axioms).
- Equations (1.1)-(1.9): all VERIFIED at honest strength (see per-row notes).
- Central definitions (backward/forward/mixed error, stability notions,
  condition number, relative residual): VERIFIED.
- Precise body prose claims: VERIFIED except the two documented non-gating
  residuals below.

Open rows (documented residuals, none gating):

1. Problem 1.7 lim-sup attainment: closed forms and the upper-bound
   direction are proved; the supremum equality is not (problems are optional
   in core mode; recorded as the chapter's honest PARTIAL).
2. S1.9 qualitative sentence that the updating-formulae error bound is
   proportional to `kappa_N`: represented by explicit trajectory budgets,
   not a `kappa_N`-shaped closed bound.
3. S1.2 correct-significant-digits digression and tablemaker's dilemma:
   unformalized definitional prose the source itself deprecates in favour of
   relative error (SKIP-OK).
4. S1.14.2 Givens QR example: empirical; its analytic anchors (Theorem
   19.10, (19.35a)) are Chapter 19 ledger rows.

## Cross-Chapter Role

Chapter 1 is the repository's foundation layer; later chapters consume:

- `FPModel` / (1.1) (`Model.lean`): the rounding model underlying every
  gamma-calculus bound in Chapters 3-28.
- `relError`, `absError`, `compRelError`, witnesses (`Error.lean`): the
  error vocabulary used by all analysis modules.
- Stability predicates (`Stability.lean`): `backwardErrorBounded`,
  `mixedForwardBackwardErrorBounded`, `isNumericallyStable`,
  condition-number surfaces, and the rule-of-thumb bridge
  `forward_from_backward` — consumed by, e.g., Chapter 7 perturbation
  theory, Chapter 9/13 LU stability (`Algorithms/LU/BlockLU.lean` uses the
  Chapter 13 vocabulary built on these), and Chapter 16-21 backward-error
  chapters.
- Lemma 1.1 and `relativeResidual2` (`PerturbationTheory.lean`): the
  normwise backward-error interpretation of residuals reused by Chapter 7
  (Theorems 7.1-7.4 in the same module), Chapter 15 condition estimation,
  and the S1.15 inverse-iteration certificate in `BeneficialRounding.lean`.
- The S1.8/S1.9/S1.14 worked analyses feed the corresponding deeper chapters
  (Chapter 4 summation, Chapter 5 polynomials, Chapter 9 GE, Chapter 19 QR)
  as motivating instances; their Chapter 1 obligations are closed here
  independently.
