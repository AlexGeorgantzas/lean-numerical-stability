# Higham Chapter 4 Source Coverage Ledger

> **Fresh strict audit and primary-source check (2026-07-19): gate PASS.**
> Equations (4.8)--(4.9) use an unparameterized `O(nu²)` term and are classified
> **DEFER–MISSING-PRECISE-STATEMENT** under the audit policy; the exact
> all-orders substitutes are recorded below and are not described as proofs of
> the printed leading-`2u` asymptotic. Higham likewise attributes the
> Algorithm 4.3 `2u` result only to "certain reasonable assumptions" without
> stating those assumptions on p. 88, so that prose bound is also
> **DEFER–MISSING-PRECISE-STATEMENT**, while the literal seven-assignment
> algorithm is verified. Equation (4.10) is closed by an actual
> magnitude-adaptive finite binary executor. Priest's 1992 thesis §4.1 was
> recovered as optional proof-source enrichment: its faithful-rounding plus
> A1/A2/S4 assumptions are represented locally, but are not retroactively
> treated as assumptions printed by Higham. See `AUDIT_ch01-28_2026-07-19.md`.

## Source and Scope

- Edition: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM, 2002).
- Chapter: 4, "Summation" (book pp. 79–92).
- Source text audited: full extracted chapter text (`ch04.txt`, pp. 79–92 including Problems 4.1–4.10).
- Mode: core. Ownership: foundational chapter, shared infrastructure for all later chapters (no split contract; audited standalone).
- Main Lean files (all under `NumStability/`):
  `Algorithms/Summation/Recursive/Core.lean`,
  `Source/Higham/Chapter04/Problem03.lean`,
  `Algorithms/Summation/Tree/Core.lean`,
  `Algorithms/Summation/Tree/Balanced.lean`,
  `Algorithms/Summation/Tree/Chain.lean`,
  `Algorithms/Summation/Pairwise/Core.lean`,
  `Algorithms/Summation/Insertion/ActiveList.lean`,
  `Algorithms/Summation/Insertion/Executor.lean`,
  `Algorithms/Summation/Insertion/Schedule.lean`,
  `Algorithms/Summation/Insertion/RunningError.lean`,
  `Algorithms/Summation/Insertion/ScheduleExecution.lean`,
  `Source/Higham/Chapter04/Section01/InsertionExamples.lean`,
  `Source/Higham/Chapter04/Section01/PairwiseSixTerm.lean`,
  `Algorithms/OrderingExamples.lean`,
  `Algorithms/Summation/Compensated.lean`,
  `Algorithms/Summation/DoublyCompensated.lean`,
  `Algorithms/NeumaierCompensatedFiniteFormat.lean`,
  `Algorithms/PriestFiniteFormat.lean`,
  `Algorithms/Summation/Accumulator.lean`,
  `Algorithms/Summation/PlusMinus.lean`,
  `Algorithms/WilkinsonAttainability.lean`, `Algorithms/Problem44SixTerm.lean`,
  `Algorithms/AitkenDenominator.lean`, `Algorithms/GridPoints.lean`,
  `Algorithms/LogExpProduct.lean`, `Analysis/Summation/ErrorBounds.lean`,
  `Analysis/FloatingPointArithmetic.lean` (two-sum / Problem 4.6 kernels).
- Axiom spot-check (2026-07-16): `recursiveSum_running_error_bound`,
  `SumTree.backward_error`, `pairwiseSum_forward_error_bound`,
  `finiteCorrectionFormulaTrace_exact_of_base2_abs_gt`,
  `fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_higham_cap`,
  `wilkinsonProblem42_ieeeDouble_abs_error_eq_defect` — all
  `[propext, Classical.choice, Quot.sound]`.
- **Historical 2026-07-14 selected-scope PASS — superseded by the present
  source/executor audit.** The finite-format
  Kahan wrappers reproduce the printed constants, but their types still require
  per-step representability/order/range or exact-correction premises. The fresh
  executor audit therefore defers (4.8)--(4.9) for lack of a precise source
  remainder. The new adaptive literal Neumaier executor closes (4.10).
  Algorithm 4.3's executor is literal and verified; its attributed `2u` prose
  is deferred because Higham does not enumerate the "certain reasonable
  assumptions" needed to make it a precise theorem. The current strict gate is
  PASS.

## Primary labels

| Label | Printed statement | Status | Lean decls | Scope notes |
|---|---|---|---|---|
| Algorithm 4.1 (§4.2) | General pairing summation: repeatedly remove two elements of `S`, add their rounded sum back; n−1 additions; recursive/pairwise/insertion are special cases | VERIFIED | `SumTree` (inductive), `SumTree.eval`, `SumTree.numAdds_eq` (n−1 additions), `SumTree.chainTreeSucc_eval_eq_recursiveSum` (recursive instance), `pairwiseSixTree` (`Source.Higham.Chapter04.Section01.PairwiseSixTerm`) / `fl_pairwiseSum` (`Algorithms.Summation.Pairwise.Core`) (pairwise instances), `InsertionScheduleTree.toSumTree` (insertion instance) | Arbitrary binary summation tree = arbitrary Algorithm 4.1 execution order. All three named methods are proved instances. |
| Algorithm 4.2 (§4.3, Kahan compensated summation) | The 4-line compensated loop with `e = (temp − s) + y` evaluated in displayed order; satisfies (4.8) | VERIFIED transcription / accuracy DEFERRED | Transcription: `kahanStepTrace`, `fl_kahanState`, `fl_kahanSum` (displayed order enforced step-by-step); final-corrected p. 85 variant `fl_kahanFinalCorrectedSum`; no-guard modified p. 86 variant `fl_kahanModifiedNoGuardSum` (0.46 trick transcribed). Analysis: see (4.8)/(4.9) rows | Algorithm transcription VERIFIED at printed strength. The unparameterized asymptotic accuracy display is deferred; exact substitute surfaces are recorded below. |
| Algorithm 4.3 (§4.3, Priest doubly compensated summation) | Sort by decreasing magnitude; displayed 7-assignment loop. Higham then attributes the `2u` result, for `n ≤ β^(t−3)`, under "certain reasonable assumptions". | VERIFIED transcription / accuracy **DEFER–MISSING-PRECISE-STATEMENT** | Abstract trace: `priestSortedByDecreasingAbs`, `PriestState`, `priestStepTrace`, `fl_priestSum`; literal executor: `priestFinite_stepTrace`, `priestFinite_prefixState`, `priestFinite_sum`; source-local facts: `priestFinite_sourceFaithful`, `priestSource_smallFirst_pair_exact`, `priestSource_pair_exact`, `priestFinite_stepDefect_eq_combineDefect`, `priestFinite_stepDefect_abs_le_combine` | The actual ten primitive operations implementing the seven displayed assignments are transcribed with explicit no-exception conditions and proved equal to the analytic trace. Higham p. 88 does not enumerate the "certain reasonable assumptions", so the attributed `2u` prose has no unique book-level theorem statement. Priest thesis §4.1 supplies faithful+A1+A2+S4 as a partial proof foundation, not assumptions imported into Higham's statement. |

## Numbered equations

| Eq. | Printed content | Status | Lean decls | Scope notes |
|---|---|---|---|---|
| (4.1) | T̂_i = (x_{i1}+y_{i1})/(1+δ_i), \|δ_i\| ≤ u, i = 1:n−1 (model (2.5) at each addition) | VERIFIED | `SumTree.inverseEvalModel`, `inverseRelErrorModel` (Analysis/FloatingPointArithmetic) | The inverse-form (2.5) witness is carried as an explicit hypothesis at every internal node, exactly as the printed derivation assumes it; the abstract `FPModel` contract supplies only the (2.4)-form `model_add`, so this is the honest rendering. |
| (4.2) | E_n := S_n − Ŝ_n = Σ_{i=1}^{n−1} δ_i T̂_i | VERIFIED | `SumTree.runningErrorContribution_eq_error` (general Algorithm 4.1), `recursiveSum_error_decomp` (per-input form for the recursive chain) | Exact local-error decomposition, general tree. |
| (4.3) | \|E_n\| ≤ u Σ_{i=1}^{n−1} \|T̂_i\| (running error bound) | VERIFIED | General: `SumTree.running_error_bound_from_inverse_models`, `running_error_sum_bound_from_inverse_models` with budget `SumTree.runningErrorBudget` (= Σ\|T̂_i\| by `computedInternalSums_abs_sum_eq_runningErrorBudget`). Recursive chain, unconditional in `FPModel`: `recursiveSum_running_error_bound` with `fl_partialSums` | The recursive-chain version needs no (2.5) hypothesis (it uses `model_add` directly with pre-rounding partial sums, which is the same bound to within the (2.4)/(2.5) reading of T̂). |
| (4.4) | \|E_n\| ≤ (n−1)u Σ\|x_i\| + O(u²); backward error x_i(1+ε_i), \|ε_i\| ≤ γ_{n−1} | VERIFIED | `recursiveSum_backward_error`, `recursiveSum_forward_error_bound` (exact γ_{n−1} radius, no O(u²) slack); general Algorithm 4.1: `SumTree.backward_error_n_minus_one`, `SumTree.forward_error_n_minus_one`; depth-refined `SumTree.backward_error` (γ_depth) | Proved form γ_{n−1} is strictly stronger than the printed first-order display. The "no x_i takes part in more than n−1 additions" backward result is the tree-depth argument (`SumTree.depth_le`). |
| (4.5) | Example x = [1, M, 2M, −3M], fl(1+M) = M: increasing/Psum give 0, decreasing gives exact 1; budgets µ = 4M, 3M, M+1 | VERIFIED | `OrderingExamples` p91 family: `p91Increasing_heavyCancellationAtLeast`, `p91Psum_heavyCancellationAtLeast`, `p91Decreasing_heavyCancellationAtLeast`, `p91_decreasing_beats_increasing_under_heavyCancellation`, `p91_decreasing_beats_psum_under_heavyCancellation`, budget comparisons around line 4090 | Conditional on the displayed absorption hypotheses (`fl_add 1 M = M`, `fl_add M (2M) = 3M`, `fl_add (−3M) (2M) = −M`, …), which is precisely the printed premise "M so large that fl(1+M) = M". |
| (4.6) | Pairwise: \|E_n\| ≤ γ_{log₂ n} Σ\|x_i\| | VERIFIED | `pairwiseSum_backward_error`, `pairwiseSum_forward_error_bound` (γ_r for n = 2^r); general n: `fl_clog2PairwiseSum`, `clog2PairwiseSum_backward_error`, `clog2PairwiseSum_forward_error_bound` (γ_⌈log₂n⌉ via zero-padding); one-signed relError corollaries | Both the printed n = 2^r derivation and the general-n ⌈log₂ n⌉ form. |
| (4.7) | Two-sum correction exactness: for rounded binary arithmetic with \|a\| ≥ \|b\|, ê = fl((a−ŝ)+b) satisfies a + b = ŝ + ê (Dekker/Knuth) | VERIFIED (finite-format, no-over/underflow scope) | `finiteCorrectionFormulaTrace_exact_of_base2_abs_le` is the literal non-strict source statement for finite binary round-to-even, β = 2, t > 1, and `finiteNormalRange (a+b)`, backed by `FastTwoSumFiniteCertificate.of_base2_abs_le`. The strict engine is `...abs_gt`; the new equality branch proves `b=a` or `b=-a`, so the first add is the representable `2a` or `0`. | The former strict-order packaging gap is closed. `finiteNormalRange (a+b)` remains the explicit no-overflow/no-underflow scope corresponding to the source's ideal rounded arithmetic. Honesty guards `correctionFormulaAbstractCounterexample_not_exact` and `noGuardCorrectionFormulaCounterexample_not_exact` prove (4.7) false in the bare relative-error/no-guard models. |
| (4.8) | Knuth: Ŝ_n = Σ(1+µ_i)x_i, \|µ_i\| ≤ 2u + O(nu²) for Algorithm 4.2 | **DEFER–MISSING-PRECISE-STATEMENT** | Conditional exact routes: `fl_kahanSum_backward_error_source_bound_of_affine_residualBudget` (radius `2u + (9+(72+C)n)u²` given a propagated retained-correction budget), `fl_kahanSum_backward_error_source_bound_of_sourceCoeff_s_bound`; leading-3u closed propagation `highamCh4KahanSuffixMajorant_propagate_of_localFacts`. Impossibility guard: `not_forall_fl_kahanSum_backward_error_source_bound_bare_fpmodel_exactSubConstants` | The source does not quantify the hidden constant or asymptotic family. The exact all-orders results are substitutes, not a claim that the printed leading-`2u` display has been proved. In the bare `FPModel` the analogous claim is false, so finite-format structure is essential. |
| (4.9) | \|E_n\| ≤ (2u + O(nu²)) Σ\|x_i\| (forward form of (4.8)) | **DEFER–MISSING-PRECISE-STATEMENT** | `fl_kahanSum_forward_error_bound_of_backward`, `fl_kahanSum_relError_le_of_backward_oneSigned`; `fl_kahanFinalCorrectedSum_forward_error_bound_of_backward` | The algebraic forward bridge is proved. The unparameterized remainder inherits (4.8)'s policy defer. |
| (4.10) | Kielbasiński/Neumaier variant (corrections accumulated separately): \|µ_i\| ≤ 2u + n²u², provided nu ≤ 0.1 | VERIFIED (literal finite binary executor, no-exception scope) | `neumaierFinite_sum`, `neumaierFinite_step_exact`, `neumaierFinite_sum_eq_neumaierFF_sum`, `neumaierFinite_backward_error_higham410`; canonical theorem `fl_recursiveResidualCorrectedSum_backward_error_higham410` | The magnitude-adaptive branch constructs the required (4.7) operand order; it is no longer an assumed step-order trace. All operations in the headline executor are `finiteRoundToEvenOp`. The remaining hypotheses are explicit source/no-exception range conditions for main, correction-accumulation, and final additions, plus the printed `nu ≤ 0.1`. |

## Central definitions and body prose claims

| Row | Status | Lean decls / reason |
|---|---|---|
| Recursive summation loop (§4.1) | VERIFIED | `fl_recursiveSum` (Fin.foldl, first add exact via `fl_add_zero`). |
| Pairwise/cascade summation (§4.1), ⌈log₂ n⌉ stages | VERIFIED | `fl_pairwiseSum` (n = 2^r), `pairwiseCarryTree`/`fl_clog2PairwiseSum` (general n); depth facts `pairwiseCarryTree_depth`, `clog2_le_pred`. |
| Insertion method (§4.1), incl. 1-2-4-8 → recursive example and sorted-inputs → pairwise example | VERIFIED | Reusable loop: `fl_insertionSumList`, `insertIncreasingAbs`, `insertionStep` under `Algorithms/Summation/Insertion/`; source examples: powers-of-two trace `1248 → 348 → 78 → 15` in `Source/Higham/Chapter04/Section01/InsertionExamples.lean`, with backward/forward/running bounds. |
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
| §4.6 item 1: Priest sorted-decreasing double-precision claim \|S_n − Ŝ_n\| ≤ 2u\|S_n\| for n ≤ β^(t−3) | **DEFER–MISSING-PRECISE-STATEMENT** | Same attributed result as Algorithm 4.3; Higham supplies only "under certain reasonable assumptions" on p. 88. The literal executor and thesis-derived local foundation are recorded in `PriestFiniteFormat.lean`. |
| §4.6 items 2–4 (method choice advice) | VERIFIED (where precise) | nu one-signed claim: `SumTree.relError_le_n_mul_u_of_oneSigned`, `recursiveSum_relError_le_n_mul_u_of_oneSigned`; log₂n vs n constants: (4.4)/(4.6) rows; compensated "constant of order 1": inherits (4.8) PARTIAL. |
| §4.7 Notes and references | SKIP-OK (bibliographic) | — |

## Problems (optional in core mode)

| Problem | Status | Lean decls / notes |
|---|---|---|
| 4.1 (condition number of summation) | VERIFIED | `summationConditionNumber` (= Σ\|x_i\|/\|Σx_i\|), `summationConditionNumber_eq`, `summationConditionNumber_eq_one_of_oneSigned` (value 1 iff one-signed data), perturbation lemma `summationComponentwisePerturbation_abs_error_le` (`Analysis/Summation/ErrorBounds.lean`). |
| 4.2 (Wilkinson: (4.3)/(4.4) nearly attainable) | VERIFIED | `WilkinsonAttainability.lean`: exact Wilkinson input family (`wilkinsonProblem42Input`), IEEE-double machine-checked run `wilkinsonProblem42_ieeeDouble_finiteRecursiveSum_eq_pow`, attained error `wilkinsonProblem42_ieeeDouble_abs_error_eq_defect` with closed form, first-order bound within factor 3 + u (`wilkinsonProblem42_ieeeDouble_first_order_bound_le_three_abs_error_plus_u`). Axiom-clean. |
| 4.3 (variable-γ expansion of recursive summation; best ordering) | VERIFIED | `recursiveSum_problem43_variableGamma` (displayed θ-expansion with \|θ_k\| ≤ γ_k = ku/(1−ku)), `recursiveSum_problem43_abs_error_bound` (displayed bound), ordering answer `recursiveSum_problem43_increasingAbs_weightedBound_le_perm` (increasing \|x_i\| minimizes, via rearrangement). |
| 4.4 (six terms {1,2,3,4,M,−M}, fl(10+M) = M) | VERIFIED | `Problem44SixTerm.lean`: exhaustive answer `problem44_outputs_exactly_Icc` / `problem44PossibleOutputs_eq_Icc` — possible outputs are precisely {0,1,…,10}, both containment and attainability over all 6! orders, in the absorbing-large-M model matching the printed premise. |
| 4.5 (± method pros/cons) | VERIFIED (discussion problem) | `Algorithms/Summation/PlusMinus.lean`: `fl_plusMinusRecursiveSum`, pro: `plusMinusPositive_conditionNumber_eq_one` (each half perfectly conditioned), error composition `plusMinus_final_add_error_bound`, `fl_plusMinusRecursiveSum_relError_bound` (con: final cancellation governs). |
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
  matching Higham's printed no-guard-digit caveats. The unparameterized
  (4.8)/(4.9) remainder is policy-deferred. Equation (4.10) is independently
  closed by the magnitude-adaptive literal finite executor, which produces the
  (4.7) operand order instead of assuming it.
- The finite-format theorem now matches the source's non-strict order exactly:
  `finiteCorrectionFormulaTrace_exact_of_base2_abs_le`; its explicit
  normal-range guard records the usual no-overflow/no-underflow scope.
- Docstring citations were checked against attached statements for every row
  above; no docstring-only coverage was counted.

## Strict gate conclusion (fresh source/executor audit, 2026-07-19)

- **(4.7) is closed at the printed non-strict order** by
  `finiteCorrectionFormulaTrace_exact_of_base2_abs_le`; this also relaxes the
  finite Kahan wrappers' order premise from `<` to `≤`.
- **(4.8)/(4.9) are DEFER–MISSING-PRECISE-STATEMENT.** Page 85 explicitly says the Kahan correction is
  not necessarily exact because (4.7)'s magnitude order need not hold, and then
  states Knuth's backward result anyway. The current
  `kahanFF_kahanSum_backward_error` still assumes a per-step order/range trace;
  it is therefore a useful exact conditional theorem, but the source gives no
  hidden constant or family with which to state a unique closure target.
- **(4.10) is closed** by `neumaierFinite_backward_error_higham410` for a
  literal finite binary magnitude-adaptive executor. Its branch produces the
  FastTwoSum order; only explicit no-exception range conditions and the printed
  `nu ≤ 0.1` remain.
- **Algorithm 4.3's displayed algorithm is verified.** The attributed `2u`
  accuracy prose is **DEFER–MISSING-PRECISE-STATEMENT**, not OPEN: Higham p. 88
  says only "under certain reasonable assumptions" and does not list them.
  `PriestFiniteFormat.lean` supplies the literal executor and source-local
  faithful/A1/A2/S4 foundation recovered from Priest's thesis, without
  pretending those assumptions were printed by Higham.

Non-gating residuals: the normal-range proviso on (4.7), Problem 4.6's general
representability packaging, the policy-deferred (4.8)/(4.9) and Algorithm 4.3
accuracy prose, and the Problem 4.10 IEEE run completion.

## Cross-chapter role

Chapter 4 is load-bearing infrastructure for essentially every later chapter:

- `Analysis/Summation/ErrorBounds.lean` (`fl_sum_error`, `fl_sum_error_tight`,
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
