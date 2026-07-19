# Higham Chapter 4 Source Coverage Ledger

> **Fresh strict audit and primary-source check (2026-07-18): gate FAIL.**
> Algorithm 4.3 accuracy and equations (4.8)-(4.10) retain exact-step,
> step-order/range, or target-scale defect hypotheses not produced by their
> rounded finite-format executors. Priest's 1992 thesis was recovered and read
> directly: its §4.1 proof assumes faithful rounding together with arithmetic
> properties A1, A2, and S4, then uses the sorted input order and
> `n ≤ β^(t-3)`. Those properties and the resulting accumulation lemma are not
> yet represented and instantiated by the repository's finite-format model. A
> documented reduction is not closure. See `AUDIT_ch01-28_2026-07-18.md`.

## Source and Scope

- Edition: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM, 2002).
- Chapter: 4, "Summation" (book pp. 79–92).
- Source text audited: full extracted chapter text (`ch04.txt`, pp. 79–92 including Problems 4.1–4.10).
- Mode: core. Ownership: foundational chapter, shared infrastructure for all later chapters (no split contract; audited standalone).
- Main Lean files (all under `LeanFpAnalysis/FP/`):
  `Algorithms/RecursiveSum.lean`, `Algorithms/SumTree.lean`, `Algorithms/PairwiseSum.lean`,
  `Algorithms/InsertionSum.lean`, `Algorithms/OrderingExamples.lean`,
  `Algorithms/CompensatedSum.lean`, `Algorithms/DoublyCompensatedSum.lean`,
  `Algorithms/AccumulatorSum.lean`, `Algorithms/PlusMinusSum.lean`,
  `Algorithms/WilkinsonAttainability.lean`, `Algorithms/Problem44SixTerm.lean`,
  `Algorithms/AitkenDenominator.lean`, `Algorithms/GridPoints.lean`,
  `Algorithms/LogExpProduct.lean`, `Analysis/Summation.lean`,
  `Analysis/FloatingPointArithmetic.lean` (two-sum / Problem 4.6 kernels).
- Axiom spot-check (2026-07-16): `recursiveSum_running_error_bound`,
  `SumTree.backward_error`, `pairwiseSum_forward_error_bound`,
  `finiteCorrectionFormulaTrace_exact_of_base2_abs_gt`,
  `fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_higham_cap`,
  `wilkinsonProblem42_ieeeDouble_abs_error_eq_defect` — all
  `[propext, Classical.choice, Quot.sound]`.
- **Historical 2026-07-14 selected-scope PASS — superseded.** The finite-format
  Kahan wrappers reproduce the printed constants, but their types still require
  per-step representability/order/range or exact-correction premises. The fresh
  executor audit therefore does not count (4.8)-(4.10) as closed. Algorithm 4.3
  is reduced in `PriestAccuracy.lean` and `PriestDefectBounded.lean`, but neither
  the stronger `PriestAllStepsExact` premise nor the weaker accumulated
  `priestDB_defectBudget` is produced from the source's faithful-arithmetic
  assumptions and size cap. The current strict gate is FAIL.

## Primary labels

| Label | Printed statement | Status | Lean decls | Scope notes |
|---|---|---|---|---|
| Algorithm 4.1 (§4.2) | General pairing summation: repeatedly remove two elements of `S`, add their rounded sum back; n−1 additions; recursive/pairwise/insertion are special cases | VERIFIED | `SumTree` (inductive), `SumTree.eval`, `SumTree.numAdds_eq` (n−1 additions), `SumTree.chainTreeSucc_eval_eq_recursiveSum` (recursive instance), `PairwiseSum.pairwiseSixTree`/`fl_pairwiseSum` (pairwise instance), `InsertionScheduleTree.toSumTree` (insertion instance) | Arbitrary binary summation tree = arbitrary Algorithm 4.1 execution order. All three named methods are proved instances. |
| Algorithm 4.2 (§4.3, Kahan compensated summation) | The 4-line compensated loop with `e = (temp − s) + y` evaluated in displayed order; satisfies (4.8) | PARTIAL | Transcription: `kahanStepTrace`, `fl_kahanState`, `fl_kahanSum` (displayed order enforced step-by-step); final-corrected p. 85 variant `fl_kahanFinalCorrectedSum`; no-guard modified p. 86 variant `fl_kahanModifiedNoGuardSum` (0.46 trick transcribed). Analysis: see (4.8)/(4.9) rows | Algorithm transcription VERIFIED at printed strength. The attached accuracy result (4.8) is conditional only — see equations table. |
| Algorithm 4.3 (§4.3, Priest doubly compensated summation) | Sort by decreasing magnitude; 7-assignment loop; if n ≤ β^(t−3) the computed sum satisfies \|s_n − ŝ_n\| ≤ 2u\|s_n\| | PARTIAL | Transcription: `priestSortedByDecreasingAbs`, `PriestState`, `priestStepTrace` (all 7 assignments in displayed parenthesized order), `fl_priestSum`, `fl_priestCorrection`; reductions: `PriestAccuracy.lean`, `PriestDefectBounded.lean` | The algorithm and algebraic/defect invariants are compiled, but the endpoint still assumes `PriestAllStepsExact` or `priestDB_defectBudget`. The recovered primary proof identifies the missing non-target source bridge precisely: faithful rounding plus A1/A2/S4 and `n ≤ β^(t−3)` must imply the accumulated defect budget. |

## Numbered equations

| Eq. | Printed content | Status | Lean decls | Scope notes |
|---|---|---|---|---|
| (4.1) | T̂_i = (x_{i1}+y_{i1})/(1+δ_i), \|δ_i\| ≤ u, i = 1:n−1 (model (2.5) at each addition) | VERIFIED | `SumTree.inverseEvalModel`, `inverseRelErrorModel` (Analysis/FloatingPointArithmetic) | The inverse-form (2.5) witness is carried as an explicit hypothesis at every internal node, exactly as the printed derivation assumes it; the abstract `FPModel` contract supplies only the (2.4)-form `model_add`, so this is the honest rendering. |
| (4.2) | E_n := S_n − Ŝ_n = Σ_{i=1}^{n−1} δ_i T̂_i | VERIFIED | `SumTree.runningErrorContribution_eq_error` (general Algorithm 4.1), `recursiveSum_error_decomp` (per-input form for the recursive chain) | Exact local-error decomposition, general tree. |
| (4.3) | \|E_n\| ≤ u Σ_{i=1}^{n−1} \|T̂_i\| (running error bound) | VERIFIED | General: `SumTree.running_error_bound_from_inverse_models`, `running_error_sum_bound_from_inverse_models` with budget `SumTree.runningErrorBudget` (= Σ\|T̂_i\| by `computedInternalSums_abs_sum_eq_runningErrorBudget`). Recursive chain, unconditional in `FPModel`: `recursiveSum_running_error_bound` with `fl_partialSums` | The recursive-chain version needs no (2.5) hypothesis (it uses `model_add` directly with pre-rounding partial sums, which is the same bound to within the (2.4)/(2.5) reading of T̂). |
| (4.4) | \|E_n\| ≤ (n−1)u Σ\|x_i\| + O(u²); backward error x_i(1+ε_i), \|ε_i\| ≤ γ_{n−1} | VERIFIED | `recursiveSum_backward_error`, `recursiveSum_forward_error_bound` (exact γ_{n−1} radius, no O(u²) slack); general Algorithm 4.1: `SumTree.backward_error_n_minus_one`, `SumTree.forward_error_n_minus_one`; depth-refined `SumTree.backward_error` (γ_depth) | Proved form γ_{n−1} is strictly stronger than the printed first-order display. The "no x_i takes part in more than n−1 additions" backward result is the tree-depth argument (`SumTree.depth_le`). |
| (4.5) | Example x = [1, M, 2M, −3M], fl(1+M) = M: increasing/Psum give 0, decreasing gives exact 1; budgets µ = 4M, 3M, M+1 | VERIFIED | `OrderingExamples` p91 family: `p91Increasing_heavyCancellationAtLeast`, `p91Psum_heavyCancellationAtLeast`, `p91Decreasing_heavyCancellationAtLeast`, `p91_decreasing_beats_increasing_under_heavyCancellation`, `p91_decreasing_beats_psum_under_heavyCancellation`, budget comparisons around line 4090 | Conditional on the displayed absorption hypotheses (`fl_add 1 M = M`, `fl_add M (2M) = 3M`, `fl_add (−3M) (2M) = −M`, …), which is precisely the printed premise "M so large that fl(1+M) = M". |
| (4.6) | Pairwise: \|E_n\| ≤ γ_{log₂ n} Σ\|x_i\| | VERIFIED | `pairwiseSum_backward_error`, `pairwiseSum_forward_error_bound` (γ_r for n = 2^r); general n: `fl_clog2PairwiseSum`, `clog2PairwiseSum_backward_error`, `clog2PairwiseSum_forward_error_bound` (γ_⌈log₂n⌉ via zero-padding); one-signed relError corollaries | Both the printed n = 2^r derivation and the general-n ⌈log₂ n⌉ form. |
| (4.7) | Two-sum correction exactness: for rounded binary arithmetic with \|a\| ≥ \|b\|, ê = fl((a−ŝ)+b) satisfies a + b = ŝ + ê (Dekker/Knuth) | VERIFIED (with scope notes) | `finiteCorrectionFormulaTrace_exact_of_base2_abs_gt` (finite binary round-to-even format, β = 2, t > 1, \|b\| < \|a\|, a+b in finite normal range), via `FastTwoSumFiniteCertificate.of_base2_abs_gt`; tie/exact-add branch `finiteCorrectionFormulaTrace_exact_of_exact_add`; trace def `correctionFormulaTrace`/`finiteCorrectionFormulaTrace` | Residuals: (i) stated for strict \|b\| < \|a\|; the \|a\| = \|b\| tie is only covered through the exact-add branch (in binary a+b is then representable, but that packaging step is not a standalone theorem); (ii) `finiteNormalRange (a+b)` side condition (bars overflow/subnormal, as the printed remark implicitly does). Honesty guards: `correctionFormulaAbstractCounterexample_not_exact` and `noGuardCorrectionFormulaCounterexample_not_exact` prove (4.7) FAILS in the bare relative-error model and under no guard digit — matching the printed p. 85 remark. NOTE: the module-header sentence "remains a finite-format proof target" is stale relative to these theorems. |
| (4.8) | Knuth: Ŝ_n = Σ(1+µ_i)x_i, \|µ_i\| ≤ 2u + O(nu²) for Algorithm 4.2 | PARTIAL | Conditional routes: `fl_kahanSum_backward_error_source_bound_of_affine_residualBudget` (radius 2u + (9+(72+C)n)u² given a propagated retained-correction budget), `fl_kahanSum_backward_error_source_bound_of_sourceCoeff_s_bound` (hypothesis-carrying); leading-3u closed propagation `highamCh4KahanSuffixMajorant_propagate_of_localFacts` (2u+... form for currently-available local facts, docstring states it does NOT close the printed leading-2u). Impossibility guard: `not_forall_fl_kahanSum_backward_error_source_bound_bare_fpmodel_exactSubConstants` | The printed 2u + O(nu²) is NOT closed unconditionally. Proved: in the bare `FPModel` (no guard-digit structure) the bound is FALSE (explicit biased-model counterexample), so any closure must use finite-format structure — consistent with Higham's own remark that (4.8) fails under the no-guard-digit model. The genuine finite binary round-to-even proof remains open. |
| (4.9) | \|E_n\| ≤ (2u + O(nu²)) Σ\|x_i\| (forward form of (4.8)) | PARTIAL | `fl_kahanSum_forward_error_bound_of_backward`, `fl_kahanSum_relError_le_of_backward_oneSigned` (algebraic bridge from any (4.8)-witness); `fl_kahanFinalCorrectedSum_forward_error_bound_of_backward` for the corrected variant | Bridge is proved; inherits the (4.8) conditionality. The one-signed "compensated summation guarantees perfect relative accuracy for nu ≤ 1" advice (§4.6 item 3) inherits the same residual. |
| (4.10) | Kielbasiński/Neumaier variant (corrections accumulated separately): \|µ_i\| ≤ 2u + n²u², provided nu ≤ 0.1 | PARTIAL | `fl_alternativeCompensatedSum` (p. 85 variant transcribed), `fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_higham_cap` — exactly the printed radius 2u + n²u² under the printed proviso nu ≤ 1/10, conditional on each step's correction formula being exact (`hexact`, i.e., step-level (4.7)); budget forms `..._of_exact_steps_correction_running_error_higham_cap`, `alternativeCompensatedCorrectionRunningErrorBudget_of_pointwise_partialSums`; guard `not_forall_alternativeCompensated_globalGammaRadius_le_two_u_add_n_sq_u_sq_of_nu_le_tenth` | Printed constants and proviso are reproduced exactly; the residual hypothesis is precisely the finite-format (4.7) exactness at each step (which `finiteCorrectionFormulaTrace_exact_of_base2_abs_gt` supplies under its order/range conditions, but the composed finite-format instantiation is not yet assembled). |

## Central definitions and body prose claims

| Row | Status | Lean decls / reason |
|---|---|---|
| Recursive summation loop (§4.1) | VERIFIED | `fl_recursiveSum` (Fin.foldl, first add exact via `fl_add_zero`). |
| Pairwise/cascade summation (§4.1), ⌈log₂ n⌉ stages | VERIFIED | `fl_pairwiseSum` (n = 2^r), `pairwiseCarryTree`/`fl_clog2PairwiseSum` (general n); depth facts `pairwiseCarryTree_depth`, `clog2_le_pred`. |
| Insertion method (§4.1), incl. 1-2-4-8 → recursive example and sorted-inputs → pairwise example | VERIFIED | `fl_insertionSumList`, `insertIncreasingAbs`, `insertionStep`; powers-of-two trace `1248 → 348 → 78 → 15` (InsertionSum ~11349–11499) with its backward/forward/running bounds. |
| Backward result ε_i ≤ γ_{n−1} (after (4.4)) | VERIFIED | `recursiveSum_backward_error`, `SumTree.backward_error_n_minus_one`. |
| Design criterion "minimize Σ\|T̂_i\|" | SKIP-OK (editorial) | Embodied by `runningErrorBudget` machinery; NP-hardness citation [708] not in scope. |
| Psum ordering (greedy min partial sums), O(n log n) comparisons | VERIFIED | `psumOrder`, `PsumGreedyOrderFrom.head_min`, `psumOrderComparisonCost` (OrderingExamples). |
| Increasing ordering optimal a-priori bound for one-signed data | VERIFIED (first-order scope) | `increasingAbsSort_recursiveExactPrefixBudget_le`, `recursiveSum_problem43_increasingAbs_weightedBound_le_perm` (rearrangement/Antivary argument); budgets compared at exact intermediate sums, the printed first-order reading. |
| Decreasing ordering attractive under heavy cancellation (extrapolated from (4.5)) | VERIFIED (example-level) | p91 theorems above; `heavyCancellation_postCancellation_bound_beats_competitor`. The general prose extrapolation is heuristic — example-level formalization is the printed content. |
| Harmonic sum "converges" in fp | SKIP-OK (illustrative prose) | No formalization; machine-behavior anecdote. |
| Insertion method minimizes bound (4.3) over all Algorithm 4.1 instances for nonnegative x_i | VERIFIED (first-order scope) | `runningErrorBudget_exactWithUnitRoundoff_greedyInsertion_le`, `fl_insertionSumList_exactWithUnitRoundoff_greedy_runningErrorBudget_le` — minimality proved against every `SumTree` with permuted leaves, with budgets evaluated at exact intermediate sums (`exactWithUnitRoundoff`), i.e., the first-order reading of (4.3). Computed-budget minimality not claimed. |
| Figure 4.1 (significand diagram) | SKIP-OK (figure) | — |
| Gill/Møller history, Cray failure anecdote, celestial-mechanics application, Euler experiment + Figure 4.2 | SKIP-OK (prose/empirical/machine-specific) | Kahan's modified no-guard loop itself is transcribed (`fl_kahanModifiedNoGuardSum`); its "all North American machines" claim is machine-specific prose. |
| §4.4 accumulator (Wolfe/Malcolm/Ross) method | VERIFIED (transcription) | `accumulatorCascadeFrom`, `fl_accumulatorSum`, `fl_accumulatorSum_uses_decreasing_abs_order` (Malcolm's crucial decreasing-order final pass recorded); exact-arithmetic sanity theorems. Malcolm's detailed relative-error-u analysis: not formalized (machine-dependent, cited to [808]) — SKIP-OK residual. |
| §4.4 distillation algorithms | VERIFIED (transcription) | `DistillationState`, `DistillationTrace`, sum-preservation `distillationTrace_sum_preserved`, termination criterion `terminatesWithinUnitRoundoff` + `distillationTrace_finalComponent_relError_le`. Run-time claims: SKIP-OK (empirical). |
| §4.5 statistical estimates, Table 4.1 | SKIP-OK (empirical table) with partial scaffolding | Zero-mean/variance-σ² local-error model formalized: `SumTree.statisticalRunningErrorContribution_expectation_eq_zero`, `_expectation_sq_eq_sum`, `_rms_le`. The Robertazzi–Schwartz distribution-specific constants (0.20µ²n³σ² etc.) are simulation-derived — out of scope. |
| §4.6 item 1: double-then-round bound \|S_n − Ŝ_n\| ≤ u\|Ŝ_n\| + nu² Σ\|x_i\| | VERIFIED (composition form) | `fl_higherPrecisionRecursiveSum`, `fl_higherPrecisionRecursiveSum_abs_error_le_nu_sq`, `_abs_error_le_gamma` (γ-form, unconditional given the working-precision rounding contract), one-signed relError corollaries. |
| §4.6 item 1: Priest sorted-decreasing double-precision claim \|S_n − Ŝ_n\| ≤ 2u\|S_n\| for n ≤ β^(t−3) | MISSING | Same family as the Algorithm 4.3 accuracy theorem; no formalization. |
| §4.6 items 2–4 (method choice advice) | VERIFIED (where precise) | nu one-signed claim: `SumTree.relError_le_n_mul_u_of_oneSigned`, `recursiveSum_relError_le_n_mul_u_of_oneSigned`; log₂n vs n constants: (4.4)/(4.6) rows; compensated "constant of order 1": inherits (4.8) PARTIAL. |
| §4.7 Notes and references | SKIP-OK (bibliographic) | — |

## Problems (optional in core mode)

| Problem | Status | Lean decls / notes |
|---|---|---|
| 4.1 (condition number of summation) | VERIFIED | `summationConditionNumber` (= Σ\|x_i\|/\|Σx_i\|), `summationConditionNumber_eq`, `summationConditionNumber_eq_one_of_oneSigned` (value 1 iff one-signed data), perturbation lemma `summationComponentwisePerturbation_abs_error_le` (Analysis/Summation). |
| 4.2 (Wilkinson: (4.3)/(4.4) nearly attainable) | VERIFIED | `WilkinsonAttainability.lean`: exact Wilkinson input family (`wilkinsonProblem42Input`), IEEE-double machine-checked run `wilkinsonProblem42_ieeeDouble_finiteRecursiveSum_eq_pow`, attained error `wilkinsonProblem42_ieeeDouble_abs_error_eq_defect` with closed form, first-order bound within factor 3 + u (`wilkinsonProblem42_ieeeDouble_first_order_bound_le_three_abs_error_plus_u`). Axiom-clean. |
| 4.3 (variable-γ expansion of recursive summation; best ordering) | VERIFIED | `recursiveSum_problem43_variableGamma` (displayed θ-expansion with \|θ_k\| ≤ γ_k = ku/(1−ku)), `recursiveSum_problem43_abs_error_bound` (displayed bound), ordering answer `recursiveSum_problem43_increasingAbs_weightedBound_le_perm` (increasing \|x_i\| minimizes, via rearrangement). |
| 4.4 (six terms {1,2,3,4,M,−M}, fl(10+M) = M) | VERIFIED | `Problem44SixTerm.lean`: exhaustive answer `problem44_outputs_exactly_Icc` / `problem44PossibleOutputs_eq_Icc` — possible outputs are precisely {0,1,…,10}, both containment and attainability over all 6! orders, in the absorbing-large-M model matching the printed premise. |
| 4.5 (± method pros/cons) | VERIFIED (discussion problem) | `PlusMinusSum.lean`: `fl_plusMinusRecursiveSum`, pro: `plusMinusPositive_conditionNumber_eq_one` (each half perfectly conditioned), error composition `plusMinus_final_add_error_bound`, `fl_plusMinusRecursiveSum_relError_bound` (con: final cancellation governs). |
| 4.6 (Shewchuk: \|err(a,b)\| ≤ min(\|a\|,\|b\|); err is a fp number) | VERIFIED (min half) / PARTIAL (representability half) | Min bound at printed strength: `nearestRoundingToFinite_add_abs_error_le_min_of_finiteSystem`, `finiteRoundToEvenOp_add_abs_error_le_min_of_finiteSystem` (any correctly rounded nearest addition). Representability: delivered by the `FastTwoSumFiniteCertificate` `finite_error` field, constructed unconditionally only under \|b\| < \|a\| + normal range (`of_base2_abs_gt`); the symmetric/WLOG packaging of "err(a,b) is always representable" is not a standalone theorem. |
| 4.7 (Aitken Δ² denominator: which expression) | VERIFIED | `AitkenDenominator.lean`: all three forms (a)/(b)/(c) with backward errors and majorant bounds; answer `aitkenDenominator_recommended_route_b`. |
| 4.8 (S_n = log Π e^{x_i} accuracy) | VERIFIED | `LogExpProduct.lean`: `logExpProductTrace`, `logExpProduct_final_error_eq`, `logExpProduct_composed_error` (error analysis of the exp/product/log route). |
| 4.9 (equispaced grid x_i = a + ih: methods (a)/(b)/(c)) | VERIFIED | `GridPoints.lean`: `fl_gridRecurrence` / `fl_gridDirect` / `fl_gridConvex` with per-method error bounds (`fl_gridRecurrence_error_bound`, `fl_gridDirect_error_bound`, `fl_gridConvex_error_bound`). |
| 4.10 (research problem: smallest n where decreasing-ordered compensated summation fails) | PARTIAL (research problem — absence does not gate) | Priest's six-term family formalized in CompensatedSum (§ "Higham Problem 4.10 / Priest six-term example"): `problem410PriestInput_sum_eq_two` (exact sum 2, all t), IEEE-single (t = 24) representability and first-step rounding facts. The full IEEE-single computed-sum-0 run and the open "smallest n" question are not closed (the latter is open in the literature). |

## Honest-strength notes

- All γ-form bounds are proved with the exact `gamma fp k = ku/(1−ku)` radius
  under explicit `gammaValid` side conditions — stronger than the printed
  first-order `ku + O(u²)` displays; no hidden target-equivalent hypotheses
  were found in the (4.1)–(4.6) rows.
- The (4.1)-form inverse model is an explicit hypothesis (`inverseEvalModel`)
  because the repository's abstract `FPModel` provides only the (2.4)-form
  contract; this mirrors the printed use of model (2.5) and is honest. The
  recursive-chain instance (`recursiveSum_running_error_bound`) needs no such
  hypothesis.
- The compensated-summation file is exceptionally candid: it contains proved
  impossibility theorems showing that (4.7) and (4.8) are FALSE in the bare
  relative-error model (`correctionFormulaAbstractCounterexample_not_exact`,
  `not_forall_fl_kahanSum_backward_error_source_bound_bare_fpmodel_exactSubConstants`),
  matching Higham's printed no-guard-digit caveats. What remains open is the
  genuinely finite-format binary proof of (4.8)/(4.9), and the assembly of the
  finite-format (4.7) theorem into the (4.10) step-exactness hypothesis.
- The CompensatedSum module-header line "the binary exactness theorem
  a + b = s + e remains a finite-format proof target" is stale: the theorem is
  now present (`finiteCorrectionFormulaTrace_exact_of_base2_abs_gt`).
- Docstring citations were checked against attached statements for every row
  above; no docstring-only coverage was counted.

## Superseded 2026-07-14 assessment (historically reported PASS with one residual)

The stricter 2026-07-18 source-strength gate at the top of this ledger replaces
this historical assessment and is `FAIL`.

**Update (2026-07-14 audit-closure):**

- **(4.8)/(4.9)/(4.10) CLOSED** in `LeanFpAnalysis/FP/Algorithms/KahanCompensatedFiniteFormat.lean`
  under the finite binary round-to-even format (β=2, round-to-nearest-even): `kahanFF_kahanSum_backward_error`
  (Ŝ_n=Σ(1+µ_i)x_i, |µ_i|≤2u+O(nu²)), `kahanFF_kahanSum_forward_error` (4.9), and
  `kahanFF_alternativeCompensatedSum_backward_error` (4.10, 2u+n²u² under nu≤1/10). The per-step (4.7)
  two-sum exactness is discharged from `finiteCorrectionFormulaTrace_exact_of_base2_abs_gt`. This is the
  finite-format model the printed source itself requires (the bare-FPModel impossibility theorems remain as
  honesty guards). The accuracy bounds carry NO smuggled hypothesis on µ.

- **Algorithm 4.3 (Priest) — ONE remaining research-grade residual, now sharpened.**
  `LeanFpAnalysis/FP/Algorithms/PriestAccuracy.lean` first reduced the printed `|s_n−ŝ_n| ≤ 2u|s_n|`
  (n≤β^{t−3}, sorted decreasing) to `PriestAllStepsExact` (per-step exactness). **Follow-up (2026-07-17):**
  `LeanFpAnalysis/FP/Algorithms/PriestDefectBounded.lean` REMOVES the exactness idealization: it *derives*
  the wrong-orientation FastTwoSum defect bound `|(y+u)−(c+x)| ≤ (u+O(u²))|x|` from the relative-error
  model alone (`priestDB_twoSum_defect_bound`), carries a defect-bounded invariant `sₙ+cₙ = Σxᵢ + ΣEⱼ`
  through the sorted loop, and reduces the printed bound to a SINGLE strictly-weaker residual
  `priestDB_defectBudget` (`|cₙ| + Σⱼ|Eⱼ| ≤ 2u|Σxᵢ|`; proved implied by `PriestAllStepsExact`). The only
  un-formalized step is the sorted-order + n≤β^{t−3} magnitude accounting that discharges that budget
  (Priest 1992 thesis §4.1) — a genuine research-grade faithful-rounding argument, allowed BLOCKED
  terminal residual, no smuggling.

Honest non-gating PARTIAL residuals: (4.7) tie case |a|=|b| and normal-range proviso; Problem 4.6
representability half; Problem 4.10 IEEE run completion.

## Cross-chapter role

Chapter 4 is load-bearing infrastructure for essentially every later chapter:

- `Analysis/Summation.lean` (`fl_sum_error`, `fl_sum_error_tight`,
  `summationConditionNumber`) is the core input to Chapter 3/5 dot-product and
  polynomial kernels (`DotProduct.lean`, `Horner.lean`) and hence to the
  Chapters 7–19 matrix-algorithm error analyses (MatVec, MatMul, LU, QR,
  Cholesky, GJE Ch14 clusters all consume the γ-form summation lemmas).
- `SumTree` running-error machinery is reused by `TreeDotProduct.lean` and the
  Ch3 running-error-bound (§3.3) framework.
- `fl_recursiveSum` is the reference accumulator for the mixed-precision and
  extended-precision dot-product modules (`ExtendedPrecisionDotProduct.lean`,
  BLAS-style kernels) and the Ch27/RandNLA summation consumers.
- The two-sum/FastTwoSum finite-format kernels built here
  (`FastTwoSumFiniteCertificate`, correction-formula exactness) are the
  foundation for any future compensated-arithmetic work (Ch5 compensated
  Horner, extended-precision iterative refinement in Ch12).
