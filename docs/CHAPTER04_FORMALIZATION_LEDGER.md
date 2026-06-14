# Chapter 4 Formalization Ledger

Source: `references/Chapter04_full.pdf` (Higham Chapter 4, 16 PDF pages,
printed pages 87--102).

Status: **FAIL for full end-to-end Chapter 4 formalization** as of this audit.
The core Algorithm 4.1 tree error analysis through equations (4.1)--(4.4) is
now represented by local Lean theorem surfaces, including the source-shaped
inverse-model running-error identity and bound, the source-shaped
carry-forward pairwise summation process from p. 88, the two displayed
insertion examples from pp. 88--89 with their inherited running-error and
one-signed bounds, the general source-level insertion active-list loop and
increasing-absolute-value invariant, explicit recursive-summation permutation
order predicates, strict-to-weak order bridges, and exact-sum preservation,
the p. 91 cancellation/order example with its displayed
computed values and running-error-budget ranking, the source-level Kahan
correction-formula trace behind equation (4.7), a local no-guard
counterexample showing that the correction-formula exactness conclusion is
not forced by model (2.6), the source-level compensated summation loop from
Algorithm 4.2 and its final-correction variant, Kahan's source-level modified
no-guard correction trace and exact-arithmetic sanity surface, the p. 94 alternative
compensated-summation trace with separately accumulated corrections, the
source-level Priest doubly
compensated summation loop from Algorithm 4.3, plus exact-gamma one-signed
relative-error corollaries for the generic tree, recursive, and pairwise
surfaces and a source-shaped `n*u` one-signed corollary for Algorithm 4.1
under an explicit `n*(n-1)*u <= 1` smallness condition, plus a source-level
higher-precision recursive-sum-then-round trace
for Section 4.6, plus source-level accumulator-cascade and distillation
invariant/termination traces for Section 4.4.  Large theorem-bearing
parts of Sections 4.1, 4.3, 4.4,
4.5, and 4.6 remain open, especially the arbitrary-`FPModel` insertion
optimality extension, compensated summation, doubly compensated summation,
machine-dependent accumulator/distillation guarantees, statistical mean-square
Table 4.1 constant derivations, the remaining method-choice guarantees, and
Problems 4.1--4.9 from pp. 100--102.

This ledger is the authoritative gate for the local `Chapter04_full.pdf`.
A row is closed only when a matching local Lean theorem proves the mathematical
claim.  Rows marked `PROSE` are expository, bibliographic, or advice-only
unless a mathematical guarantee is explicitly stated.  Citation-only or
sketch-level proof dependencies are tracked in
`docs/CHAPTER04_PROOF_SOURCE_LEDGER.md`.

## Coverage Summary

| Source location | Claim/result | Lean status | Current Lean surface | Gap / next action |
|---|---|---:|---|---|
| p. 87 | Chapter title, epigraphs, and note. | PROSE | N/A | No theorem obligation. |
| p. 88, intro | Summation occurs in inner products, means, variances, norms, and nonlinear functions; no single method is uniformly best. | PROSE | N/A | Expository framing. |
| p. 88, recursive summation loop | Left-to-right recursive summation `s = 0; s = s + x_i`. | CLOSED | `fl_recursiveSum`, `fl_recursiveSum_exactWithUnitRoundoff`, `recursiveSum_backward_error`, `recursiveSum_forward_error_bound`, `recursiveSum_running_error_bound` | Closed for the concrete input order supplied by `v : Fin n -> Real`, including the exact-arithmetic sanity theorem that recursive summation returns the exact source sum under `FPModel.exactWithUnitRoundoff`. Psum cost comparisons and downstream error comparisons remain separate rows below. |
| p. 88, ordering dependence | Accuracy of recursive summation varies with the ordering; increasing and decreasing magnitude orderings are named. | PARTIAL | `fl_recursiveSum`, `IncreasingMagnitudeOrder`, `StrictIncreasingMagnitudeOrder`, `DecreasingMagnitudeOrder`, `StrictDecreasingMagnitudeOrder`, `IncreasingMagnitudeOrder.of_strict`, `DecreasingMagnitudeOrder.of_strict`, `fl_recursiveSumInOrder`, `sum_orderedInput_eq_sum`, `fl_recursiveSumInOrder_refl`, `DecreasingAbsList`, `insertDecreasingAbs`, `insertDecreasingAbs_perm`, `insertDecreasingAbs_preserves`, `increasingAbsSort`, `increasingAbsSort_sorted`, `increasingAbsSort_perm`, `increasingAbsSort_sum_eq`, `decreasingAbsSort`, `decreasingAbsSort_sorted`, `decreasingAbsSort_perm`, `decreasingAbsSort_sum_eq`, `increasingAbsSortVector`, `increasingAbsSortVector_sorted`, `increasingAbsSortVector_perm`, `increasingAbsSortVector_sum_eq`, `decreasingAbsSortVector`, `decreasingAbsSortVector_sorted`, `decreasingAbsSortVector_perm`, `decreasingAbsSortVector_sum_eq`, `psumOrder`, `psumOrder_perm`, `psumOrder_greedyTrace`, `psumOrder_increasingAbs_of_nonnegative`, `psumOrderVector`, `psumOrderVector_perm`, `psumOrderVector_greedyTrace`, `psumOrderVector_sorted_of_nonnegative`, `psumOrderVector_sum_eq` | Lean can now evaluate recursive summation through an explicit finite permutation, state weak and strict increasing/decreasing magnitude order predicates, bridge strict orders to the weak reusable surfaces, and prove that the exact mathematical sum is preserved by the permutation. The concrete list-level increasing/decreasing magnitude sorters are closed, and finite-vector bridges export increasing sort, decreasing sort, and Psum for `Fin n` inputs while preserving the source multiset, exact source sum, and the relevant sorted/greedy certificate. Optimized comparison-count bounds and downstream error comparisons remain open; the scan-based Psum cost is tracked in the pp. 90--91 row. |
| p. 88, pairwise summation | Pairwise/cascade/fan-in summation, odd-entry carry-forward, `ceil(log2 n)` stages, and the displayed `n = 6` parenthesization. | CLOSED | `fl_pairwiseSum`, `pairwiseSum_backward_error`, `pairwiseSum_forward_error_bound`, `pairwiseSixTree`, `fl_pairwiseSumSixDisplayed`, `fl_pairwiseSumSixDisplayed_eq`, `pairwiseSumSixDisplayed_backward_error`, `pairwiseSumSixDisplayed_forward_error_bound`, `pairwiseCarryTree`, `pairwiseCarryTree_depth`, `nat_le_two_pow_pred`, `clog2_le_pred`, `pairwiseCarryTree_depth_le_linear`, `fl_pairwiseCarrySum`, `pairwiseCarrySum_backward_error`, `pairwiseCarrySum_forward_error_bound`, `fl_clog2PairwiseSum`, `clog2PairwiseSum_backward_error`, `clog2PairwiseSum_forward_error_bound`, `SumTree.balancedTree`, `SumTree.balancedTree_forward_error` | Closed for perfect powers of two, for the displayed six-term parenthesization, for the source-shaped arbitrary-length carry-forward process, and for the zero-padded arbitrary-length variant. The carry-tree depth comparison `pairwiseCarryTree_depth_le_linear` now records that `ceil(log2 n)` is bounded by the generic `n - 1` depth for nonempty inputs. |
| pp. 88--89, insertion method | Sort by increasing magnitude, repeatedly insert the newest sum back into the ordered list; examples reduce to recursive or pairwise summation in special cases. | PARTIAL | `IncreasingAbsList`, `IncreasingAbsList.head_le_of_mem_of_nonnegative`, `insertion_first_two_exact_sum_le_head_tail_sum_of_nonnegative`, `insertion_first_two_exact_sum_le_tail_pair_sum_of_nonnegative`, `insertion_first_two_exact_sum_le_pair_sum_of_nonnegative`, `insertIncreasingAbs`, `insertIncreasingAbs_length`, `insertIncreasingAbs_ne_nil`, `insertIncreasingAbs_preserves`, `insertionStep`, `insertionStep_length_cons_cons`, `insertionStep_ne_nil_of_ne_nil`, `insertionStep_preserves_increasingAbs_cons_cons`, `insertionActiveAfter`, `insertionActiveAfter_preserves_increasingAbs`, `insertionActiveAfter_ne_nil_of_ne_nil`, `insertionActiveAfter_length_le_one_of_length_le_succ`, `insertionActiveAfter_full_length_le_one`, `insertionActiveAfter_full_length_eq_one_of_ne_nil`, `insertionActiveAfter_full_eq_singleton_of_ne_nil`, `fl_insertionSumList`, `fl_insertionSumList_eq_of_activeAfter_eq_singleton`, `fl_insertionSumList_eq_terminal_singleton_of_ne_nil`, `InsertionScheduleTree`, `InsertionScheduleTree.leafCount`, `InsertionScheduleTree.leaves_length`, `InsertionScheduleTree.toSumTree`, `InsertionScheduleTree.leafVector`, `InsertionScheduleTree.leafVector_eq_leaves_get`, `InsertionScheduleTree.toSumTree_eval`, `InsertionScheduleTree.exactEval`, `InsertionScheduleTree.exactMergeCost`, `InsertionScheduleTree.weightedLeafDepthCost`, `InsertionScheduleTree.leafDepthWeights`, `InsertionScheduleTree.weightedDepthPairsCost`, `InsertionScheduleTree.exactMergeCost_nonneg`, `InsertionScheduleTree.exactEval_eq_leaves_sum`, `InsertionScheduleTree.exactEval_eq_of_leaves_perm`, `InsertionScheduleTree.leafDepthWeights_weights_eq_leaves`, `InsertionScheduleTree.weightedLeafDepthCost_eq_weightedDepthPairsCost`, `InsertionScheduleTree.weightedLeafDepthCost_succ_eq_add_exactEval`, `InsertionScheduleTree.weightedLeafDepthCost_nonneg_of_leaves_nonnegative`, `InsertionScheduleTree.weightedLeafDepthCost_mono_startDepth_of_leaves_nonnegative`, `InsertionScheduleTree.weightedLeafDepthCost_leaf_pair_exchange_le`, `InsertionScheduleTree.weightedDepthPairsCost_pair_exchange_le`, `InsertionScheduleTree.exactEval_nonneg_of_leaves_nonnegative`, `InsertionScheduleTree.exactMergeCost_node_of_nonnegative`, `InsertionScheduleTree.exactMergeCost_eq_weightedLeafDepthCost_of_leaves_nonnegative`, `InsertionScheduleTree.eval_exactWithUnitRoundoff`, `InsertionScheduleTree.toSumTree_eval_exactWithUnitRoundoff`, `InsertionScheduleTree.toSumTree_runningErrorBudget_exactWithUnitRoundoff`, `InsertionScheduleItem`, `insertInsertionScheduleItemIncreasingAbs_values`, `insertInsertionScheduleItemIncreasingAbs_leaves_perm`, `insertionScheduleStep_values`, `insertionScheduleStep_leaves_perm`, `insertionScheduleAfter_values`, `insertionScheduleAfter_leaves_perm`, `insertionScheduleAfter_full_eq_singleton_of_ne_nil`, `fl_insertionSumList_has_list_schedule_of_ne_nil`, `fl_insertionSumList_has_sumTree_shape_of_ne_nil`, `fl_insertionSumList_has_sumTree_eval_of_ne_nil`, `fl_insertionSumList_pair`, `insertionPowersFourTree`, `insertionPowersFour_exact_order`, `fl_insertionPowersFour_eq`, `fl_insertionPowersFour_eq_recursiveSum`, `insertionPowersFour_running_error_bound_from_inverse_models`, `insertionPowersFour_relError_le_gamma_of_oneSigned`, `insertionNearOneFourTree`, `insertionNearOneFour_exact_order`, `fl_insertionNearOneFour_eq`, `fl_insertionNearOneFour_eq_pairwiseSum`, `insertionNearOneFour_running_error_bound_from_inverse_models`, `insertionNearOneFour_relError_le_gamma_of_oneSigned` | The general source-level ordered active-list loop is closed: insert-by-increasing-absolute-value preserves the active-list invariant and nonemptiness, each nonterminal step removes the two smallest active entries, adds them, reinserts the rounded sum, repeated steps preserve the invariant and nonemptiness, supplying `xs.length` fuel reaches a terminal active list of length at most one, nonempty input terminates in exactly one active value, and `fl_insertionSumList` returns that singleton terminal value. A list-shaped binary schedule trace is also closed: the schedule trace projects to the source active-list values, preserves represented source leaves up to `List.Perm`, reaches a singleton schedule item for nonempty input, `fl_insertionSumList_has_list_schedule_of_ne_nil` proves that nonempty insertion summation is represented by a binary tree whose leaves permute the original active list, and `fl_insertionSumList_has_sumTree_shape_of_ne_nil` packages the dependent `SumTree` shape, `InsertionScheduleTree.leafVector_eq_leaves_get` identifies the `Fin` source vector with the concrete leaf list, and `fl_insertionSumList_has_sumTree_eval_of_ne_nil` proves the insertion result is exactly that Algorithm 4.1 `SumTree.eval`. `InsertionScheduleTree.exactMergeCost` now records the exact sum of absolute intermediate sums, `InsertionScheduleTree.toSumTree_runningErrorBudget_exactWithUnitRoundoff` identifies it with the converted `SumTree.runningErrorBudget` under exact arithmetic, `InsertionScheduleTree.exactMergeCost_node_of_nonnegative` removes the absolute value at nonnegative merge nodes, `InsertionScheduleTree.exactMergeCost_eq_weightedLeafDepthCost_of_leaves_nonnegative` rewrites the nonnegative objective as weighted external path length, and `InsertionScheduleTree.weightedLeafDepthCost_eq_weightedDepthPairsCost` rewrites that path length as an explicit sum over leaf-depth/weight pairs. The two displayed four-entry examples are also closed, including their ordering inequalities, recursive/pairwise parenthesization equivalences, inverse-model running-error bounds, and one-signed exact-`gamma` relative-error corollaries. For nonnegative active lists sorted by increasing absolute value, `insertion_first_two_exact_sum_le_pair_sum_of_nonnegative` proves that the first two entries minimize the next exact pair sum among admissible pairs; the weighted-depth exchange lemmas now include both the bare two-leaf inequality and an arbitrary explicit leaf-depth context. The dependent `SumTree` shape bridge, value-level `SumTree.eval` transport, exact running-error-budget transport, weighted-path-length form, explicit leaf-depth rearrangement surface, concrete greedy trace, and exact-arithmetic Algorithm 4.1 comparison are closed; the arbitrary-`FPModel` computed-intermediate route choice remains open. |
| p. 89, Algorithm 4.1 | General pair-removal summation algorithm over a multiset/list of active numbers. | CLOSED | `SumTree`, `SumTree.eval`, `SumTree.exactSum` | Closed as a binary tree model of all `n - 1` pairwise-addition schedules. |
| p. 89, `n - 1` loop executions | Any Algorithm 4.1 tree with `n` leaves performs exactly `n - 1` additions. | CLOSED | `SumTree.numAdds`, `SumTree.numAdds_eq` | Closed. |
| p. 89, special cases of Algorithm 4.1 | Recursive, pairwise, and insertion methods are special cases. | CLOSED | `SumTree.chainTreeSucc`, `SumTree.chainTreeSucc_depth`, `SumTree.chainTreeSucc_eval_eq_recursiveSum`, `SumTree.chainTree`, `SumTree.chainTree_forward_error`, `SumTree.balancedTree`, `SumTree.balancedTree_forward_error`, `pairwiseSixTree`, `pairwiseCarryTree`, `fl_pairwiseCarrySum`, `fl_clog2PairwiseSum`, `fl_insertionSumList`, `InsertionScheduleTree`, `fl_insertionSumList_has_list_schedule_of_ne_nil`, `fl_insertionSumList_has_sumTree_shape_of_ne_nil`, `fl_insertionSumList_has_sumTree_eval_of_ne_nil`, `insertionPowersFourTree`, `insertionNearOneFourTree` | Recursive, power-of-two pairwise, displayed-six-term pairwise, source-shaped arbitrary-length carry-forward pairwise, zero-padded arbitrary-length scalar pairwise, the source-level insertion active-list loop, the list-shaped binary schedule trace for every nonempty insertion run, and the two displayed insertion example specializations are closed. The recursive value-level bridge is closed by `SumTree.chainTreeSucc_eval_eq_recursiveSum`, which proves the successor-indexed left-chain Algorithm 4.1 tree agrees with the literal `fl_recursiveSum` loop because the first zero-accumulator addition is exact. The dependent insertion `SumTree` shape bridge is closed by `InsertionScheduleTree.toSumTree`, and the value-level insertion special-case bridge is closed by `InsertionScheduleTree.toSumTree_eval` and `fl_insertionSumList_has_sumTree_eval_of_ne_nil`. |
| p. 89, eq. (4.1) | Each internal computed sum satisfies the inverse model `(2.5)`, `T_hat_i = T_i/(1 + delta_i)`, `|delta_i| <= u`. | CLOSED | `SumTree.inverseEvalModel` | Closed as the source-shaped operation-witness predicate. Direct derivation from the repository's generic `FPModel` is not claimed because `FPModel` stores the standard `(2.4)` model; concrete finite-format inverse witnesses are provided elsewhere by `inverseRelErrorModel` theorems. |
| p. 90, eq. (4.2) | The total error is the sum of local errors `delta_i * T_hat_i`. | CLOSED | `SumTree.runningErrorContribution`, `SumTree.exists_runningErrorContribution_of_inverseEvalModel`, `SumTree.runningErrorContribution_eq_error` | Closed for arbitrary `SumTree` schedules under the inverse-model witnesses from (4.1). |
| p. 90, eq. (4.3) | Running-error bound `|E_n| <= u * sum_i |T_hat_i|`. | CLOSED | `SumTree.runningErrorBudget`, `SumTree.runningErrorContribution_abs_le`, `SumTree.running_error_sum_bound_from_inverse_models` | Closed for arbitrary `SumTree` schedules under inverse-model witnesses. |
| p. 90, eq. (4.4) | Weaker a priori forward bound with source-uniform `n - 1` dependence and first-order expansion. | CLOSED | `SumTree.depth_le`, `SumTree.forward_error_n_minus_one`, `gamma_eq_linear_plus_quadratic_remainder` | Closed in exact gamma form `gamma (n - 1) * sum |x_i|`; the source's `O(u^2)` wording is represented by the existing exact gamma expansion rather than asymptotic notation. |
| p. 90, backward-error statement after (4.4) | Computed sum is the exact sum of perturbed inputs `x_i(1 + eps_i)` with `|eps_i| <= gamma_{n-1}`. | CLOSED | `SumTree.backward_error_n_minus_one`, `recursiveSum_backward_error`, `pairwiseSum_backward_error` | Closed for arbitrary Algorithm 4.1 trees and for the recursive/pairwise specializations. |
| p. 90, design criterion | To improve accuracy, minimize the absolute values of intermediate sums. | PROSE/PARTIAL | `SumTree.running_error_sum_bound_from_inverse_models` | The mathematical bound motivating the criterion is closed. No optimization theorem over all schedules is proved. |
| pp. 90--91, Psum and ordering discussion | Psum greedily minimizes successive partial sums, can be implemented with `O(n log n)` comparisons; increasing order is best for nonnegative recursive summation by the a priori bound. | PARTIAL | `psumSelect`, `psumSelect_perm`, `psumSelect_min`, `psumSelect_mem`, `psumSelectComparisonCost`, `psumSelectComparisonCost_eq_pred_length`, `psumSelect_le_of_nonnegative`, `psumSelect_rest_nonnegative`, `psumTriangularComparisonCost`, `psumOrderFromFuel`, `psumOrderFrom`, `psumOrder`, `psumOrderFromFuelComparisonCost`, `psumOrderFromComparisonCost`, `psumOrderComparisonCost`, `PsumGreedyOrderFrom`, `PsumGreedyOrderFrom.head_min`, `PsumGreedyOrderFrom.perm`, `psumOrderFromFuel_perm`, `psumOrderFrom_perm`, `psumOrder_perm`, `psumOrderFromFuel_greedyTrace`, `psumOrderFrom_greedyTrace`, `psumOrder_greedyTrace`, `psumOrderFromFuel_increasingAbs_of_nonnegative`, `psumOrderFrom_increasingAbs_of_nonnegative`, `psumOrder_increasingAbs_of_nonnegative`, `psumOrder_eq_increasingAbsSort_of_nonnegative`, `psumOrder_recursiveExactPrefixBudget_le`, `psumOrder_recursiveRoundedPrefixBudget_exactWithUnitRoundoff_le`, `psumOrderFromFuelComparisonCost_eq_triangular`, `psumOrderFromComparisonCost_eq_triangular`, `psumOrderComparisonCost_eq_triangular`, `psumLogSearchStepBudget`, `psumLogSearchComparisonBudget`, `PsumLogSearchTraceFrom`, `PsumLogSearchTraceFrom.greedyTrace`, `PsumLogSearchTraceFrom.perm`, `PsumLogSearchTraceFrom.cost_le_budget`, `psumLogSearchStepBudget_mono`, `psumLogSearchComparisonBudget_le_mul_stepBudget`, `psumOrderFromFuel_logSearchTrace`, `psumOrderFrom_logSearchTrace`, `psumOrder_logSearchTrace`, `psumOrder_logSearchComparisonCost_le_mul_stepBudget`, `increasingAbsSort`, `increasingAbsSort_sorted`, `increasingAbsSort_perm`, `increasingAbsSort_sum_eq`, `IncreasingAbsList.cons_of_abs_le_all`, `IncreasingAbsList.sortedLE_of_nonnegative`, `decreasingAbsSort`, `decreasingAbsSort_sorted`, `decreasingAbsSort_perm`, `decreasingAbsSort_sum_eq`, `increasingAbsSortVector`, `increasingAbsSortVector_sorted`, `increasingAbsSortVector_perm`, `increasingAbsSortVector_sum_eq`, `increasingAbsSortVector_recursiveRoundedPrefixBudget_exactWithUnitRoundoff_le`, `decreasingAbsSortVector`, `decreasingAbsSortVector_sorted`, `decreasingAbsSortVector_perm`, `decreasingAbsSortVector_sum_eq`, `psumOrderVector`, `psumOrderVector_perm`, `psumOrderVector_greedyTrace`, `psumOrderVector_sorted_of_nonnegative`, `psumOrderVector_eq_increasingAbsSortVector_of_nonnegative`, `psumOrderVector_recursiveRoundedPrefixBudget_exactWithUnitRoundoff_le`, `psumOrderVector_sum_eq`, `recursiveExactPrefixBudgetFrom`, `recursiveExactPrefixBudget`, `recursiveRoundedPrefixBudgetFrom`, `recursiveRoundedPrefixBudget`, `recursiveRoundedPrefixBudgetFrom_exactWithUnitRoundoff`, `recursiveRoundedPrefixBudget_exactWithUnitRoundoff`, `recursiveExactPrefixBudgetFrom_insertIncreasingAbs_le_cons_of_nonnegative_sorted`, `increasingAbsSort_recursiveExactPrefixBudgetFrom_le`, `increasingAbsSort_recursiveExactPrefixBudget_le`, `increasingAbsSort_recursiveRoundedPrefixBudget_exactWithUnitRoundoff_le`, `IncreasingMagnitudeOrder`, `DecreasingMagnitudeOrder`, `fl_recursiveSumInOrder`, `sum_orderedInput_eq_sum`, `HeavyCancellationAtLeast`, `relError_exact_eq_zero`, `relError_zero_eq_one_of_ne_zero`, `relError_pos_of_ne_exact`, `relError_le_of_abs_sub_le_mul_abs`, `heavyCancellation_postCancellation_bound_beats_competitor`, `heavyCancellation_exact_result_beats_inexact_result`, `heavyCancellation_exact_result_beats_zero_result`, `p91_decreasing_beats_increasing_under_heavyCancellation`, `p91_decreasing_beats_psum_under_heavyCancellation`, `p91_decreasing_postCancellation_bound_beats_increasing`, `p91_decreasing_postCancellation_bound_beats_psum` | The concrete increasing/decreasing magnitude list sorters are closed and preserve both the source multiset and exact source sum. The finite-vector bridge is closed for increasing sort, decreasing sort, and Psum by the `*Vector` surfaces, which package source-list outputs as `List.Vector ℝ n` for `Fin n` inputs while preserving the multiset, exact sum, sortedness, and greedy trace as applicable. The source-side list Psum generator is closed: each step selects an available term minimizing `|acc + x|`, the generated order preserves the source multiset, and `psumOrder_greedyTrace` realizes the successive partial-sum greedy rule. The same-sign equivalence statement is now closed for nonnegative inputs in equality form: `psumSelect_le_of_nonnegative` shows the Psum selector chooses a smallest available term, `IncreasingAbsList.sortedLE_of_nonnegative` bridges custom absolute-value order to ordinary sortedness, and `psumOrder_eq_increasingAbsSort_of_nonnegative` plus `psumOrderVector_eq_increasingAbsSortVector_of_nonnegative` prove that zero-accumulator Psum coincides with increasing-magnitude sorting for nonnegative list and finite-vector inputs. The scan-cost layer for the concrete local implementation is closed: `psumSelectComparisonCost_eq_pred_length` proves a selection over a list of length `m` uses `m - 1` comparisons, and `psumOrderComparisonCost_eq_triangular` proves the full scan-based Psum order uses the triangular count `0 + ... + (n - 1)`. The optimized log-search cost contract is now formalized separately: `PsumLogSearchTraceFrom` reuses the same Psum minimizer, `PsumLogSearchTraceFrom.greedyTrace` and `.perm` connect it to the mathematical Psum ordering, `PsumLogSearchTraceFrom.cost_le_budget` proves the recursive logarithmic selector-cost bound, and `psumOrder_logSearchComparisonCost_le_mul_stepBudget` gives the compact `n * (2 * log2 (n+1) + 1)` comparison-budget surface. The ordered-neighbor selector foundation is also closed by `PsumLowerNeighbor`, `PsumUpperNeighbor`, and `psumNeighborChoice_mem_and_min`: once a sorted/search structure exposes the predecessor and successor around `-acc`, choosing the closer one is proved to minimize the Psum objective over the active set. The nonnegative increasing/Psum ordering claim is closed both in exact a priori prefix-budget form and in exact-arithmetic recursive-loop running-budget form: `recursiveRoundedPrefixBudgetFrom_exactWithUnitRoundoff` identifies the list-shaped rounded pre-rounding budget with `recursiveExactPrefixBudgetFrom`, `increasingAbsSort_recursiveRoundedPrefixBudget_exactWithUnitRoundoff_le` and `psumOrder_recursiveRoundedPrefixBudget_exactWithUnitRoundoff_le` prove that increasing/Psum order cannot increase that equation-(4.3)-style budget for nonnegative lists, and the corresponding finite-vector bridge is closed by `psumOrderVector_recursiveRoundedPrefixBudget_exactWithUnitRoundoff_le`. The source's heavy-cancellation phrase is represented by `HeavyCancellationAtLeast`, and `heavyCancellation_exact_result_beats_inexact_result` gives a broader conditional theorem-level comparison: if two orderings have the same nonzero exact sum, one computed result is exact, and the competing result is inexact under an explicit heavy-cancellation regime, then the exact result has strictly smaller relative error. The checkable post-cancellation route is now closed by `relError_le_of_abs_sub_le_mul_abs` and `heavyCancellation_postCancellation_bound_beats_competitor`: an explicit absolute-error certificate relative to the final nonzero sum gives a relative-error bound, and any competitor with larger relative error is formally worse. The older zero-collapse surface `heavyCancellation_exact_result_beats_zero_result` remains as a special p. 91 bridge. The p. 91 increasing/Psum versus decreasing instantiations are closed both by the exact/zero-collapse route and by the post-cancellation certificate route via `p91_decreasing_postCancellation_bound_beats_increasing` and `p91_decreasing_postCancellation_bound_beats_psum`. Remaining target: instantiate the ordered-neighbor/log-search selector with a concrete balanced-search tree, including search, deletion, balance, and cost accounting. |
| p. 91, example (4.5) | For `x = [1, M, 2M, -3M]` with `fl(1+M)=M`, increasing/Psum produce `0`, decreasing produces `1`, and the displayed `mu` values rank the orderings. | CLOSED | `P91CancellationRounding`, `p91IncreasingInput`, `p91PsumInput`, `p91DecreasingInput`, `p91Increasing_sum_abs_eq`, `p91Psum_sum_abs_eq`, `p91Decreasing_sum_abs_eq`, `p91Increasing_heavyCancellationAtLeast`, `p91Psum_heavyCancellationAtLeast`, `p91Decreasing_heavyCancellationAtLeast`, `fl_p91Increasing_eq_zero`, `fl_p91Psum_eq_zero`, `fl_p91Decreasing_eq_one`, `p91Increasing_relError_eq_one`, `p91Psum_relError_eq_one`, `fl_p91Decreasing_eq_exact_sum`, `p91_decreasing_beats_increasing_under_heavyCancellation`, `p91_decreasing_beats_psum_under_heavyCancellation`, `p91Increasing_runningErrorBudget_eq`, `p91Psum_runningErrorBudget_eq`, `p91Decreasing_runningErrorBudget_eq`, `p91_runningErrorBudget_ranking` | Closed under an explicit abstract rounding certificate for the displayed local operations. The exact heavy-cancellation ratio is also closed: for nonnegative `M`, all three displayed orderings have `sum |x_i| = 1 + 6M` and exact sum `1`, hence satisfy `HeavyCancellationAtLeast` with factor `1 + 6M`. The new conditional comparison packages the relative-error conclusion: in this certified heavy-cancellation setting, decreasing order has zero relative error while increasing and Psum have relative error one, so decreasing is strictly better for the displayed example. This does not prove a general theorem that decreasing order is best under every heavy-cancellation pattern. |
| p. 91, insertion optimality | For nonnegative inputs, insertion summation minimizes the running-error bound over all Algorithm 4.1 instances. | PARTIAL | `IncreasingAbsList.head_le_of_mem_of_nonnegative`, `insertion_first_two_exact_sum_le_head_tail_sum_of_nonnegative`, `insertion_first_two_exact_sum_le_tail_pair_sum_of_nonnegative`, `insertion_first_two_exact_sum_le_pair_sum_of_nonnegative`, `InsertionScheduleTree.exactEval`, `InsertionScheduleTree.exactEval_eq_leaves_sum`, `InsertionScheduleTree.exactEval_eq_of_leaves_perm`, `InsertionScheduleTree.exactMergeCost`, `InsertionScheduleTree.weightedLeafDepthCost`, `InsertionScheduleTree.leafDepthWeights`, `InsertionScheduleTree.weightedDepthPairsCost`, `InsertionScheduleTree.exactMergeCost_nonneg`, `InsertionScheduleTree.leafDepthWeights_weights_eq_leaves`, `InsertionScheduleTree.weightedLeafDepthCost_eq_weightedDepthPairsCost`, `InsertionScheduleTree.weightedLeafDepthCost_succ_eq_add_exactEval`, `InsertionScheduleTree.weightedLeafDepthCost_nonneg_of_leaves_nonnegative`, `InsertionScheduleTree.weightedLeafDepthCost_mono_startDepth_of_leaves_nonnegative`, `InsertionScheduleTree.weightedLeafDepthCost_leaf_pair_exchange_le`, `InsertionScheduleTree.weightedDepthPairsCost_pair_exchange_le`, `InsertionScheduleTree.exactEval_nonneg_of_leaves_nonnegative`, `InsertionScheduleTree.exactMergeCost_node_of_nonnegative`, `InsertionScheduleTree.exactMergeCost_eq_weightedLeafDepthCost_of_leaves_nonnegative`, `InsertionScheduleTree.GreedyInsertionTree`, `InsertionScheduleTree.exists_greedyInsertionTree_weightedLeafDepthCost_le`, `InsertionScheduleTree.exists_greedyInsertionTree_exactMergeCost_le`, `InsertionScheduleTree.GreedyInsertionTree.weightedLeafDepthCost_le`, `InsertionScheduleTree.GreedyInsertionTree.exactMergeCost_le`, `SumTree.runningErrorBudget_exactWithUnitRoundoff_greedyInsertion_le`, `insertionScheduleAfter_full_greedy_exactWithUnitRoundoff_of_ne_nil`, `fl_insertionSumList_has_greedy_schedule_exactWithUnitRoundoff_of_ne_nil`, `fl_insertionSumList_exactWithUnitRoundoff_greedy_runningErrorBudget_le`, `InsertionScheduleTree.eval_exactWithUnitRoundoff`, `InsertionScheduleTree.toSumTree_eval_exactWithUnitRoundoff`, `InsertionScheduleTree.toSumTree_runningErrorBudget_exactWithUnitRoundoff` | The local one-step foundation is closed: in a nonnegative active list sorted by increasing absolute value, the first two entries have exact pair sum no larger than any admissible pair using the head or two tail entries. The exact-cost foundation is also closed: `InsertionScheduleTree.exactMergeCost` records the absolute intermediate-sum objective, exact evaluation is leaf-sum/permutation invariant, weighted external path length is nonnegative and monotone in starting depth for nonnegative leaves, `InsertionScheduleTree.leafDepthWeights` exposes the objective as explicit leaf-depth/weight pairs, the pairwise exchange inequality puts smaller weights at no shallower depth without increasing weighted cost both for the bare two-leaf tree and inside arbitrary explicit leaf-depth context, nonnegative merge nodes drop the absolute value, the converted dependent `SumTree.runningErrorBudget` equals that exact cost under exact arithmetic, and `InsertionScheduleTree.exactMergeCost_eq_weightedLeafDepthCost_of_leaves_nonnegative` rewrites the objective as weighted external path length. The existential and supplied-greedy Huffman/optimal-merge theorems are now closed by `InsertionScheduleTree.exists_greedyInsertionTree_weightedLeafDepthCost_le`, `InsertionScheduleTree.exists_greedyInsertionTree_exactMergeCost_le`, `InsertionScheduleTree.GreedyInsertionTree.weightedLeafDepthCost_le`, and `InsertionScheduleTree.GreedyInsertionTree.exactMergeCost_le`; `SumTree.runningErrorBudget_exactWithUnitRoundoff_greedyInsertion_le` composes the supplied-greedy exact-cost theorem with exact-arithmetic Algorithm 4.1 materialization. The concrete source-level insertion trace is now closed by `insertionScheduleAfter_full_greedy_exactWithUnitRoundoff_of_ne_nil`, `fl_insertionSumList_has_greedy_schedule_exactWithUnitRoundoff_of_ne_nil`, and `fl_insertionSumList_exactWithUnitRoundoff_greedy_runningErrorBudget_le`, which prove that exact-arithmetic insertion summation realizes a greedy schedule and has no larger exact running-error budget than any nonnegative Algorithm 4.1 tree with the same leaf multiset. Remaining route choice: the literal arbitrary-`FPModel` computed-intermediate version needs additional model/order assumptions or an explicitly exact-arithmetic theorem surface. |
| pp. 91--92, pairwise eq. (4.6) | For `n = 2^r`, pairwise summation has `gamma_{log2 n}` forward/backward bounds. | CLOSED | `fl_pairwiseSum`, `pairwiseSum_backward_error`, `pairwiseSum_forward_error_bound`, `SumTree.balancedTree_backward_error`, `SumTree.balancedTree_forward_error` | Closed for powers of two, matching the source's simplifying assumption. |
| pp. 92--93, correction formula eq. (4.7) | Binary rounded addition can recover the exact local error by the displayed parenthesized subtraction in rounded base-2 arithmetic under source assumptions. | PARTIAL | `CorrectionFormulaTrace`, `CorrectionFormulaTrace.exact`, `correctionFormulaTrace`, `correctionFormulaTrace_s`, `correctionFormulaTrace_e`, `finiteCorrectionFormulaTrace`, `finiteCorrectionFormulaTrace_s`, `finiteCorrectionFormulaTrace_e`, `finiteCorrectionFormulaTrace_exact_of_exact_sub_and_finite_error_add`, `finiteCorrectionFormulaTrace_exact_of_sterbenz_and_finite_error_add`, `finiteCorrectionFormulaTrace_exact_of_signed_sterbenz_and_finite_error_add`, `finiteCorrectionFormulaTrace_exact_of_two_signed_sterbenz`, `FastTwoSumFiniteCertificate`, `FastTwoSumFiniteCertificate.finite_s_unconditional`, `FastTwoSumFiniteCertificate.of_error_obligations`, `FastTwoSumFiniteCertificate.of_two_signed_sterbenz`, `correctionFormula_abs_order_not_imply_signed_sterbenz_exact_sum`, `FastTwoSumFiniteCertificate.of_exact_add`, `finiteCorrectionFormulaTrace_exact_of_fastTwoSumFiniteCertificate`, `finiteCorrectionFormulaTrace_exact_of_exact_add`, `FloatingPointFormat.finiteRoundToEven_eq_finiteNormalRoundToEven_of_finiteNormalRange`, `FloatingPointFormat.finiteRoundToEvenOp_eq_finiteNormalRoundToEven_of_finiteNormalRange`, `FloatingPointFormat.finiteRoundToEvenOp_add_error_finite_of_sourceRoundToEvenEvidence`, `FloatingPointFormat.binaryGuardQuotient_normalized_or_max_of_mantissaBound_le_of_lt_two_mul`, `FloatingPointFormat.sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between`, `FloatingPointFormat.sourceRoundToEvenEvidence_sameExponent_mantissa_eq_or_succ_of_bracket`, `FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem`, `FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem`, `FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_boundary_error_finiteSystem`, `FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_boundary_error_finiteSystem`, `FloatingPointFormat.sourceRoundToEvenEvidence_positive_normalizedValue_add_sameSign_sameExponent_error_finiteSystem`, `FloatingPointFormat.sourceRoundToEvenEvidence_negative_normalizedValue_add_sameSign_sameExponent_error_finiteSystem`, `FloatingPointFormat.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_sameExponent_error_finiteSystem`, `FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_sameExponent_error_finiteSystem`, `FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_alignedCoeff_lt_mantissaBound`, `FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_alignedCoeff_lt_mantissaBound`, `FloatingPointFormat.finiteRoundToEvenOp_add_oppositeSign_sameExponent_eq_exact`, `FloatingPointFormat.finiteRoundToEvenOp_add_oppositeSign_sameExponent_error_finiteSystem`, `FloatingPointFormat.finiteRoundToEvenOp_add_subnormal_eq_exact`, `FloatingPointFormat.finiteRoundToEvenOp_add_subnormal_error_finiteSystem`, `FloatingPointFormat.finiteRoundToEvenOp_add_normalized_sameSign_subnormal_error_finiteSystem_of_alignedCoeff_lt_mantissaBound`, `FloatingPointFormat.finiteRoundToEvenOp_add_subnormal_sameSign_normalized_error_finiteSystem_of_alignedCoeff_lt_mantissaBound`, `FloatingPointFormat.finiteRoundToEvenOp_add_neg_right_finiteSystem_eq_exact_of_sterbenzRatioCondition`, `FloatingPointFormat.finiteRoundToEvenOp_add_neg_right_finiteSystem_error_finiteSystem_of_sterbenzRatioCondition`, `FloatingPointFormat.finiteRoundToEvenOp_add_neg_left_finiteSystem_eq_exact_of_sterbenzRatioCondition`, `FloatingPointFormat.finiteRoundToEvenOp_add_neg_left_finiteSystem_error_finiteSystem_of_sterbenzRatioCondition`, `correctionFormulaAbstractCounterexampleFPModel`, `correctionFormulaAbstractCounterexample_abs_order`, `correctionFormulaAbstractCounterexample_not_exact` | The source-level rounded trace `s = fl(a + b); e = fl((a - s) + b)` is closed. The concrete finite round-to-even trace is closed by `finiteCorrectionFormulaTrace`, and equation (4.7)'s exactness conclusion is proved under explicit finite-format routes including exact intermediate subtraction, positive and signed Sterbenz, two signed Sterbenz certificates, exact first add, and a packaged `FastTwoSumFiniteCertificate`. `FastTwoSumFiniteCertificate.finite_s_unconditional` proves the first rounded sum is finite, while `FastTwoSumFiniteCertificate.of_error_obligations` narrows the future certificate proof to representability of `a-s` and `(a+b)-s`. The finite-normal source branch is connected to the total finite selector by `FloatingPointFormat.finiteRoundToEven_eq_finiteNormalRoundToEven_of_finiteNormalRange` and `FloatingPointFormat.finiteRoundToEvenOp_eq_finiteNormalRoundToEven_of_finiteNormalRange`, source-policy finite local errors now transfer to the concrete add operation by `FloatingPointFormat.finiteRoundToEvenOp_add_error_finite_of_sourceRoundToEvenEvidence`, and the base-2 guard-word quotient dispatch is closed by `FloatingPointFormat.binaryGuardQuotient_normalized_or_max_of_mantissaBound_le_of_lt_two_mul`; same-exponent endpoint selection is connected to lower/upper mantissa indices by `FloatingPointFormat.sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between` and `FloatingPointFormat.sourceRoundToEvenEvidence_sameExponent_mantissa_eq_or_succ_of_bracket`; and the positive, negative, and max-mantissa exponent-boundary aligned guard-word branches now compose through to finite representability of the local roundoff error by `FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem`, `FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem`, `FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_boundary_error_finiteSystem`, and `FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_boundary_error_finiteSystem`. Actual same-sign same-exponent normalized operands now feed that guard-word split directly through `FloatingPointFormat.sourceRoundToEvenEvidence_positive_normalizedValue_add_sameSign_sameExponent_error_finiteSystem`, `FloatingPointFormat.sourceRoundToEvenEvidence_negative_normalizedValue_add_sameSign_sameExponent_error_finiteSystem`, `FloatingPointFormat.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_sameExponent_error_finiteSystem`, and the finite-normal operation wrapper `FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_sameExponent_error_finiteSystem`. The coefficient-fits same-sign normalized ordered-exponent branch is also exact with finite zero local error in both operand orders. Opposite-sign same-exponent normalized addition, all-subnormal arbitrary-sign addition, and the coefficient-fits same-sign mixed normal/subnormal subcase are exact zero-error branches by `FloatingPointFormat.finiteRoundToEvenOp_add_oppositeSign_sameExponent_error_finiteSystem`, `FloatingPointFormat.finiteRoundToEvenOp_add_subnormal_error_finiteSystem`, and the two mixed operand-order finite-error wrappers. The finite-system Sterbenz add-neg wrappers close exact zero-error branches for `x + (-y)` and `(-y) + x`, including subnormal and mixed finite operands, whenever a `sterbenzRatioCondition` is available. The failed shortcuts are also recorded: `correctionFormula_abs_order_not_imply_signed_sterbenz_exact_sum` rules out deriving the first signed Sterbenz branch directly from `|b| < |a|`, and `correctionFormulaAbstractCounterexample_not_exact` rules out the abstract-standard-model route. Remaining target: prove `finiteRoundToEvenOp_add_error_finite_of_base2_abs_order_of_finiteNormalRange` by deriving the remaining normalized different-exponent and mixed normal/subnormal inexact-alignment splits needed to feed the operation-level handoff, then use the acquired Shewchuk/Dekker split to derive the full finite base-2 all-signs TwoSum/FastTwoSum certificate. Original Dekker/Knuth/Linnainmaa theorem bodies remain unacquired. See `docs/CHAPTER04_C44_CORRECTION_FORMULA_BOTTLENECK.md` and `docs/CHAPTER04_PROOF_SOURCE_LEDGER.md`. |
| pp. 92--93, correction formula route-failure audit | Finite-normal range alone cannot prove the missing roundoff-error representability lemma for equation (4.7). | CLOSED | `FloatingPointFormat.binaryT2DoubleRounding_neg_three_sixteenths_not_finiteSystem`, `FloatingPointFormat.binaryT2DoubleRounding_roundoff_error_not_finiteSystem`, `FloatingPointFormat.binaryT2DoubleRounding_21_16_finiteNormalRange`, `FloatingPointFormat.finiteNormalRange_not_enough_for_roundoff_error_finiteSystem` | The tiny binary `t = 2` format gives a local Lean counterexample to the tempting shortcut: `21/16` is inside the finite-normal range and rounds directly to `3/2`, but the exact real error `-3/16` is not a finite-system value. Therefore the next C4.4 theorem must exploit the stronger Shewchuk/Dekker hypothesis that the rounded source value is the exact addition of finite binary operands, not merely an arbitrary in-range real. |
| pp. 92--93, correction formula coefficient-grid subdependency | Same-exponent finite binary operand-grid information can imply finite representability of a local error coefficient. | CLOSED | `FloatingPointFormat.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound` | This closes the first reusable coefficient-level handoff for the remaining C4.4 FastTwoSum route: if the exact source value and rounded endpoint are expressed on the same signed scaled-integer exponent lattice and their integer coefficient gap has fewer than `t` radix digits, then the real error is finite representable. The full roundoff-error lemma still has to derive that shared lattice exponent and coefficient-gap bound from the actual finite binary operands and adjacent round-to-even endpoint. |
| pp. 92--93, correction formula certificate finite-error handoff | Same-exponent coefficient-grid information discharges the `FastTwoSumFiniteCertificate.finite_error` field. | CLOSED | `FastTwoSumFiniteCertificate.finite_error_of_sameExponentScaledInteger` | This closes the direct certificate-level handoff for the true local error: once `a+b` and `fl(a+b)` have a common signed scaled-integer exponent lattice representation and the coefficient gap fits in `t` radix digits, the certificate field `fmt.finiteSystem ((a+b)-fl(a+b))` follows immediately. The full C4.4 source theorem still has to derive those common-lattice and coefficient-gap hypotheses from the printed finite binary operand assumptions and round-to-even adjacency proof. |
| pp. 92--93, correction formula aligned operand-grid source subdependency | Same-sign, same-exponent normalized operands give an exact source sum on the common exponent lattice with a one-guard-digit coefficient, the aligned exact-add branch is closed when the coefficient fits, the binary lower/upper endpoint coefficient-gap arithmetic is closed for the inexact guard-word branch, source round-to-even evidence is connected to lower/upper same-exponent endpoint selection, and both positive and negative aligned same-sign guard-word finite-error compositions are closed. | CLOSED | `FloatingPointFormat.normalizedValue_add_sameSign_sameExponent_eq_scaledInteger`, `FloatingPointFormat.normalizedMantissa_add_lt_two_mul_mantissaBound`, `FloatingPointFormat.normalizedValue_add_sameSign_sameExponent_exists_scaledIntegerCoeff`, `FloatingPointFormat.normalizedValue_add_sameSign_sameExponent_finiteSystem_of_add_lt_mantissaBound`, `FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_sameExponent_eq_exact_of_add_lt_mantissaBound`, `FloatingPointFormat.finiteRoundToEvenOp_add_error_finite_of_sourceRoundToEvenEvidence`, `FloatingPointFormat.binaryGuardQuotient_normalized_or_max_of_mantissaBound_le_of_lt_two_mul`, `FloatingPointFormat.binaryGuardCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_ceil`, `FloatingPointFormat.normalizedValue_succExponent_eq_beta_scaledInteger`, `FloatingPointFormat.binaryGuardSource_between_sameExponentEndpoints_positive`, `FloatingPointFormat.binaryGuardSource_between_sameExponentEndpoints_negative`, `FloatingPointFormat.sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between`, `FloatingPointFormat.sourceRoundToEvenEvidence_sameExponent_mantissa_eq_or_succ_of_bracket`, `FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_mantissa_eq_or_succ_of_bracket`, `FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_coeffDiff_natAbs_lt_mantissaBound`, `FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem`, `FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_mantissa_eq_or_succ_of_bracket`, `FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_coeffDiff_natAbs_lt_mantissaBound`, `FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem`, `FloatingPointFormat.sourceRoundToEvenEvidence_positive_normalizedValue_add_sameSign_sameExponent_error_finiteSystem`, `FloatingPointFormat.sourceRoundToEvenEvidence_negative_normalizedValue_add_sameSign_sameExponent_error_finiteSystem`, `FloatingPointFormat.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_sameExponent_error_finiteSystem`, `FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_sameExponent_error_finiteSystem` | This closes the source-side aligned normalized addition fact for the remaining C4.4 route: if `a = sign*m*beta^(e-t)` and `b = sign*n*beta^(e-t)` with normalized `t`-digit mantissas, then `a+b = sign*(m+n)*beta^(e-t)` and `m+n < 2*beta^t`. If `m+n < beta^t`, the exact source sum is finite representable and the finite round-to-even add is exact. For the binary guard-word case, `binaryGuardQuotient_normalized_or_max_of_mantissaBound_le_of_lt_two_mul` dispatches the quotient to either an ordinary normalized bracket or the max-mantissa exponent-boundary branch, `binaryGuardCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_ceil` proves that lower quotient or non-exact upper quotient endpoint selection yields a `t`-digit roundoff coefficient, the source-policy endpoint lemmas prove that actual source round-to-even evidence inside a same-exponent adjacent bracket selects mantissa `q` or `q+1`, and the positive/negative aligned same-sign compositions construct the quotient brackets, handle the exact-remainder endpoint, and directly discharge the local roundoff-error finite-system obligation. The operand-level wrappers `FloatingPointFormat.sourceRoundToEvenEvidence_positive_normalizedValue_add_sameSign_sameExponent_error_finiteSystem`, `FloatingPointFormat.sourceRoundToEvenEvidence_negative_normalizedValue_add_sameSign_sameExponent_error_finiteSystem`, and `FloatingPointFormat.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_sameExponent_error_finiteSystem` now derive the guard coefficient hypotheses directly from normalized operands and close both signs. `FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_sameExponent_error_finiteSystem` transfers the aligned source finite-error witness to the concrete finite-normal rounded-add operation. The rounded-add error theorem still has to cover the other operand-alignment/sign and subnormal boundary split cases. |
| pp. 92--93, correction formula normalized ordered-exponent exact subdependency | Same-sign normalized operands with ordered exponents add exactly when the higher-exponent operand shifted onto the lower exponent lattice plus the lower mantissa fits in `t` radix digits. | CLOSED | `FloatingPointFormat.normalizedValue_add_sameSign_orderedExponent_finiteSystem_of_alignedCoeff_lt_mantissaBound`, `FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_orderedExponent_eq_exact_of_alignedCoeff_lt_mantissaBound`, `FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_alignedCoeff_lt_mantissaBound`, `FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_eq_exact_of_alignedCoeff_lt_mantissaBound`, `FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_alignedCoeff_lt_mantissaBound` | This closes the coefficient-fits normalized different-exponent subcase for the remaining C4.4 rounded-add error route. The high exponent operand is rewritten on the lower exponent lattice with coefficient `mHigh * beta^(eHigh-eLow)`; if adding the lower mantissa keeps the total below `beta^t`, the exact source sum is finite representable. Both operand orders of the concrete finite round-to-even add return the exact source sum and have finite zero local error. The full rounded-add error theorem still has to cover normalized different-exponent inexact guard/alignment cases. |
| pp. 92--93, correction formula normalized ordered-exponent one-guard subdependency | Same-sign normalized operands with ordered exponents have finite local add error when the aligned lower-lattice coefficient lies in the binary one-guard range. | CLOSED | `FloatingPointFormat.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_guardCoeffBounds`, `FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_guardCoeffBounds`, `FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_guardCoeffBounds` | This closes the next normalized different-exponent subcase for the remaining C4.4 rounded-add error route. The high exponent operand is shifted to the lower exponent lattice, producing coefficient `mHigh * beta^(eHigh-eLow) + mLow`. Under base `2`, if this coefficient is between `beta^t` and `2*beta^t`, source round-to-even evidence feeds the existing guard-coefficient dispatcher, and the finite-normal operation wrapper transfers finite local-error representability to both operand orders of the concrete rounded add. The full rounded-add error theorem still has to cover larger normalized alignment gaps outside this one-guard range and mixed inexact alignment. |
| pp. 92--93, correction formula opposite-sign same-exponent source subdependency | Opposite-sign normalized operands with the same exponent reduce to exact same-exponent subtraction, so the rounded add has zero local error. | CLOSED | `FloatingPointFormat.finiteRoundToEvenOp_add_oppositeSign_sameExponent_eq_exact`, `FloatingPointFormat.finiteRoundToEvenOp_add_oppositeSign_sameExponent_error_finiteSystem` | This closes another sign branch for the remaining C4.4 rounded-add error route: `fmt.normalizedValue negative m e + fmt.normalizedValue (!negative) n e` is rewritten as same-sign same-exponent subtraction, the existing finite-system subtraction theorem proves exact representability, and the concrete finite round-to-even add returns the exact source value. The full rounded-add error theorem still has to cover different-exponent alignment and subnormal boundary cases. |
| pp. 92--93, correction formula all-subnormal addition subdependency | Subnormal operands of arbitrary signs add exactly under the concrete finite round-to-even operation, so the local roundoff error is zero. | CLOSED | `FloatingPointFormat.subnormalValue_add_sameSign_finiteSystem_of_subnormalMantissas`, `FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_subnormal_eq_exact`, `FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_subnormal_error_finiteSystem`, `FloatingPointFormat.finiteRoundToEvenOp_add_oppositeSign_subnormal_eq_exact`, `FloatingPointFormat.finiteRoundToEvenOp_add_oppositeSign_subnormal_error_finiteSystem`, `FloatingPointFormat.finiteRoundToEvenOp_add_subnormal_eq_exact`, `FloatingPointFormat.finiteRoundToEvenOp_add_subnormal_error_finiteSystem` | This closes the all-subnormal branch for the remaining C4.4 rounded-add error route. Same-sign subnormal addition stays on the common subnormal lattice with coefficient `m+n < beta^t`; opposite signs reduce to the already proved same-sign subnormal subtraction finite-system theorem. Therefore the concrete finite round-to-even add returns the exact source sum for arbitrary signs, and the local error is finite zero. The full rounded-add error theorem still has to cover normalized different-exponent alignment and mixed normal/subnormal boundary cases. |
| pp. 92--93, correction formula mixed normal/subnormal exact subdependency | Same-sign mixed normal/subnormal operands add exactly when the normalized operand shifted to the subnormal lattice plus the subnormal coefficient fits in `t` radix digits. | CLOSED | `FloatingPointFormat.normalizedValue_add_sameSign_subnormal_finiteSystem_of_alignedCoeff_lt_mantissaBound`, `FloatingPointFormat.finiteRoundToEvenOp_add_normalized_sameSign_subnormal_eq_exact_of_alignedCoeff_lt_mantissaBound`, `FloatingPointFormat.finiteRoundToEvenOp_add_normalized_sameSign_subnormal_error_finiteSystem_of_alignedCoeff_lt_mantissaBound`, `FloatingPointFormat.finiteRoundToEvenOp_add_subnormal_sameSign_normalized_eq_exact_of_alignedCoeff_lt_mantissaBound`, `FloatingPointFormat.finiteRoundToEvenOp_add_subnormal_sameSign_normalized_error_finiteSystem_of_alignedCoeff_lt_mantissaBound` | This closes the coefficient-fits mixed boundary subcase for the remaining C4.4 rounded-add error route. The normalized operand is rewritten on the `emin` subnormal lattice with coefficient `m * beta^(e-emin)`; if adding the subnormal coefficient keeps the total below `beta^t`, the exact source sum is finite representable. Both operand orders of the concrete finite round-to-even add therefore return the exact source sum and have finite zero local error. The full rounded-add error theorem still has to cover mixed alignment outside the one-guard range and normalized different-exponent alignment. |
| pp. 92--93, correction formula mixed normal/subnormal one-guard subdependency | Same-sign mixed normal/subnormal operands have finite local add error when the aligned subnormal-lattice coefficient lies in the binary one-guard range. | CLOSED | `FloatingPointFormat.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_guardCoeffBounds`, `FloatingPointFormat.finiteRoundToEvenOp_add_normalized_sameSign_subnormal_error_finiteSystem_of_guardCoeffBounds`, `FloatingPointFormat.finiteRoundToEvenOp_add_subnormal_sameSign_normalized_error_finiteSystem_of_guardCoeffBounds` | This closes the mixed analogue of the normalized ordered-exponent one-guard branch. The normalized operand is shifted onto the `emin` subnormal lattice, producing coefficient `m * beta^(e-emin) + n`. Under base `2`, if this coefficient is between `beta^t` and `2*beta^t`, source round-to-even evidence feeds the existing guard-coefficient dispatcher at exponent `emin`, and the finite-normal operation wrappers transfer finite local-error representability to both operand orders of the concrete rounded add. The full rounded-add error theorem still has to cover alignment outside this one-guard range and remaining opposite-sign/magnitude splits. |
| pp. 92--93, correction formula exact-or-one-guard dispatch subdependency | Same-sign normalized ordered-exponent and mixed normal/subnormal operands have finite local add error under one combined aligned-coefficient bound `alignedCoeff < 2*beta^t`. | CLOSED | `FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_alignedCoeff_lt_two_mul_mantissaBound`, `FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_alignedCoeff_lt_two_mul_mantissaBound`, `FloatingPointFormat.finiteRoundToEvenOp_add_normalized_sameSign_subnormal_error_finiteSystem_of_alignedCoeff_lt_two_mul_mantissaBound`, `FloatingPointFormat.finiteRoundToEvenOp_add_subnormal_sameSign_normalized_error_finiteSystem_of_alignedCoeff_lt_two_mul_mantissaBound` | This packages the exact and one-guard branches into reusable operation-level dispatchers. Each theorem splits on whether the aligned coefficient is below `beta^t`; the small branch reuses the exact zero-error theorem, while the complementary branch reuses the one-guard finite-error theorem with `beta^t <= alignedCoeff < 2*beta^t`. The full rounded-add error theorem now needs the remaining alignment cases at or above `2*beta^t` and the unresolved opposite-sign/magnitude splits. |
| pp. 92--93, correction formula normalized Sterbenz opposite-sign subdependency | Normalized positive `x` and `y` satisfying Sterbenz's ratio condition give exact rounded addition for `x + (-y)`, hence zero local error. | CLOSED | `FloatingPointFormat.finiteRoundToEvenOp_add_neg_right_normalizedSystem_eq_exact_of_sterbenzRatioCondition`, `FloatingPointFormat.finiteRoundToEvenOp_add_neg_right_normalizedSystem_error_finiteSystem_of_sterbenzRatioCondition`, `FloatingPointFormat.finiteRoundToEvenOp_add_neg_right_positive_normalizedValue_eq_exact_of_sterbenzRatioCondition`, `FloatingPointFormat.finiteRoundToEvenOp_add_neg_right_positive_normalizedValue_error_finiteSystem_of_sterbenzRatioCondition` | This packages the opposite-sign normalized addition branch as exact Sterbenz subtraction. It closes exact/error finite-system obligations whenever the branch has a proved `sterbenzRatioCondition x y`; the remaining FastTwoSum work is to derive such branch conditions, or the guard-word finite-error condition, from the printed finite base-2 operand assumptions and magnitude/alignment split. |
| pp. 92--93, correction formula finite-system Sterbenz opposite-sign subdependency | Finite operands satisfying Sterbenz's ratio condition give exact rounded addition for `x + (-y)` and the commuted form `(-y) + x`, hence zero local error across normal, subnormal, and mixed branches. | CLOSED | `FloatingPointFormat.finiteRoundToEvenOp_add_neg_right_finiteSystem_eq_exact_of_sterbenzRatioCondition`, `FloatingPointFormat.finiteRoundToEvenOp_add_neg_right_finiteSystem_error_finiteSystem_of_sterbenzRatioCondition`, `FloatingPointFormat.finiteRoundToEvenOp_add_neg_left_finiteSystem_eq_exact_of_sterbenzRatioCondition`, `FloatingPointFormat.finiteRoundToEvenOp_add_neg_left_finiteSystem_error_finiteSystem_of_sterbenzRatioCondition` | This extends the normalized Sterbenz add-neg exact branch to arbitrary finite operands by reusing the all-case finite-system Sterbenz subtraction theorem. It closes the subnormal and mixed finite branches once the proof context supplies `sterbenzRatioCondition x y`; the remaining FastTwoSum work is to derive those ratio/branch conditions, or the guard-word finite-error route, from the printed base-2 operand assumptions. |
| pp. 92--93, correction formula exponent-boundary guard-word subdependency | The aligned guard-word branch remains controlled when the upper rounded endpoint crosses from `maxNormalMantissa` to `minNormalMantissa` at the next exponent. | CLOSED | `FloatingPointFormat.binaryGuardQuotient_normalized_or_max_of_mantissaBound_le_of_lt_two_mul`, `FloatingPointFormat.normalizedValue_add_twoExponent_eq_beta_sq_scaledInteger`, `FloatingPointFormat.binaryGuardSource_between_boundaryEndpoints_positive`, `FloatingPointFormat.binaryGuardSource_between_boundaryEndpoints_negative`, `FloatingPointFormat.binaryGuardBoundaryCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_boundary`, `FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_boundary_coeffDiff_natAbs_lt_mantissaBound`, `FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_boundary_coeffDiff_natAbs_lt_mantissaBound`, `FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_boundary_error_finiteSystem`, `FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_boundary_error_finiteSystem`, `FloatingPointFormat.finiteRoundToEvenOp_add_error_finite_of_sourceRoundToEvenEvidence` | This closes the max-mantissa exponent-boundary case for the aligned C4.4 guard-word route: the quotient dispatcher identifies `q = maxNormalMantissa` as the boundary case, the next-binade endpoint is shifted onto the original source lattice, positive and negative real-order boundary brackets are constructed, exact remainder zero still forces the lower endpoint, and the selected endpoint coefficient has a `t`-digit gap that discharges finite representability of the local roundoff error. The finite-normal operation-level handoff is closed; the rounded-add error theorem still has to derive the remaining alignment/sign and subnormal cases that feed it. |
| p. 93, Algorithm 4.2 | Kahan compensated summation loop. | CLOSED | `KahanState`, `KahanStepTrace`, `kahanStepTrace`, `kahanStep`, `kahanStepTrace_temp`, `kahanStepTrace_y`, `kahanStepTrace_s`, `kahanStepTrace_e`, `kahanStepTrace_correctionFormulaTrace`, `kahanStepTrace_compensated_total_eq_of_exact_y_and_correction`, `kahanStep_compensated_total_eq_of_exact_y_and_correction`, `kahanPrefixState_compensated_total_eq_sum_of_exact_steps`, `fl_kahanState_compensated_total_eq_sum_of_exact_steps`, `fl_kahanSum_add_correction_eq_sum_of_exact_steps`, `kahanPrefixState`, `kahanTrace`, `fl_kahanState`, `fl_kahanSum`, `fl_kahanCorrection` | Closed as the source-level rounded trace, including `temp`, `y`, `s`, and `e` updates with the displayed evaluation order. The local connection to equation (4.7) is also closed: each Kahan step's `(s,e)` pair is exactly the correction-formula trace applied to `temp` and `y`; if the `y = x + e` add and that correction formula are exact, the step preserves the compensated total as `new s + new e = old s + x + old e`. The prefix invariant is now closed as well: if those local exactness hypotheses hold at every processed step, the final compensated total `s + e`, equivalently `fl_kahanSum + fl_kahanCorrection`, equals the exact prefix/source sum. No global stability bound is claimed here. |
| pp. 93--94, eqs. (4.8)--(4.9) and final-correction variant | Knuth/Kahan compensated summation backward bound and corresponding forward bound with constant essentially independent of `n` when `nu < 1`; Kahan's variant appends `s = s + e` and admits a stronger bound. | PARTIAL | `fl_kahanFinalCorrectedSum`, `fl_kahanFinalCorrectedSum_eq_add_correction`, `fl_kahanFinalCorrectedSum_eq_sum_of_exact_steps_and_final_add`, `fl_kahanState_exactWithUnitRoundoff`, `fl_kahanSum_exactWithUnitRoundoff`, `fl_kahanCorrection_exactWithUnitRoundoff`, `fl_kahanFinalCorrectedSum_exactWithUnitRoundoff`, `kahanStepTrace_correctionFormulaTrace`, `kahanStepTrace_compensated_total_eq_of_exact_y_and_correction`, `kahanStep_compensated_total_eq_of_exact_y_and_correction`, `kahanPrefixState_compensated_total_eq_sum_of_exact_steps`, `fl_kahanState_compensated_total_eq_sum_of_exact_steps`, `fl_kahanSum_add_correction_eq_sum_of_exact_steps`, `kahan_backward_error_forward_bound_core`, `fl_kahanSum_forward_error_bound_of_backward`, `fl_kahanSum_relError_le_of_backward_oneSigned`, `fl_kahanFinalCorrectedSum_forward_error_bound_of_backward`, `fl_kahanFinalCorrectedSum_relError_le_of_backward_oneSigned` | The p. 93 final-correction variant is closed as the source-level rounded final add `s = s + e`. The zero-roundoff sanity surface is closed: under exact arithmetic, Kahan's final state is the exact source sum with zero retained correction, and both the ordinary and final-corrected returned sums equal the exact source sum. The local exactness bridge from equation (4.7) into Algorithm 4.2 is closed: every Kahan step's correction pair is the correction-formula trace for `temp` and `y`, exact `y` plus exact correction formula preserves the compensated total across that step, and the prefix invariant lifts this to `final s + final e = exact sum` when every step satisfies the local exactness hypotheses. The final-correction exactness corollary is also closed: if the appended `s+e` rounded add is exact under those hypotheses, the final-corrected returned value is the exact source sum. The algebraic bridge from a supplied Kahan-style backward-error representation to the corresponding forward bound is now closed for both ordinary and final-corrected returned sums, including the one-signed relative-error corollary. The Knuth/Kahan backward-error witnesses for (4.8), the concrete constant in (4.9), the stronger final-correction witness bound, and their finite/rounded arithmetic assumptions remain open. |
| p. 94, alternative compensated summation eq. (4.10) | Separate accumulated corrections give a weaker second-order term under `nu < 0.1`; divide-and-conquer extends the range. | PARTIAL | `AlternativeCompensatedStepTrace`, `alternativeCompensatedStepTrace`, `alternativeCompensatedStepTrace_temp`, `alternativeCompensatedStepTrace_s`, `alternativeCompensatedStepTrace_e`, `alternativeCompensatedStepTrace_correctionFormulaTrace`, `alternativeCompensatedStepTrace_main_plus_correction_eq_of_correction`, `alternativeCompensatedPrefixCorrection`, `alternativeCompensatedPrefixSum_add_corrections_eq_sum_of_exact_steps`, `fl_alternativeCompensatedMainSum_add_exact_corrections_eq_sum_of_exact_steps`, `fl_alternativeCompensatedSum_eq_sum_of_exact_steps_and_exact_correction_sum`, `alternativeCompensatedPrefixSum`, `alternativeCompensatedTrace`, `alternativeCompensatedCorrections`, `fl_alternativeCompensatedMainSum`, `fl_alternativeCompensatedGlobalCorrection`, `fl_alternativeCompensatedSum`, `fl_alternativeCompensatedMainSum_exactWithUnitRoundoff`, `alternativeCompensatedCorrections_exactWithUnitRoundoff`, `fl_alternativeCompensatedGlobalCorrection_exactWithUnitRoundoff`, `fl_alternativeCompensatedSum_exactWithUnitRoundoff`, `fl_alternativeCompensatedSum_forward_error_bound_of_backward`, `fl_alternativeCompensatedSum_relError_le_of_backward_oneSigned` | The p. 94 variant is closed as a source-level trace: local corrections are stored separately, recursively summed, and then added to the computed main sum. The local connection to equation (4.7) is now closed for this variant too: each stored correction pair is exactly the correction-formula trace for `temp` and the current input, and exact local correction gives `new main sum + stored correction = old main sum + x_i`. The loop-level exact-correction invariant is also closed: if every local correction formula is exact, then the final main sum plus the exact sum of stored corrections equals the exact source sum; if the recursive global-correction accumulation and final main-plus-correction add are exact too, the final alternative compensated value is exact. The zero-roundoff sanity surface is closed: under exact arithmetic, the main sum is exact, every stored local correction is zero, the global correction is zero, and the final returned value is the exact source sum. The algebraic bridge from a supplied equation-(4.10)-style backward-error representation to the corresponding forward bound and one-signed relative-error corollary is closed. The actual (4.10) perturbation witnesses, its `nu < 0.1` hypotheses, and the divide-and-conquer extension remain open pending proof-source acquisition. |
| pp. 94--95, no-guard-digit comments and Kahan machine-dependent variant | Standard compensated summation can fail under no-guard arithmetic; Kahan's modified correction has machine-dependent guarantees. | PARTIAL | `NoGuardCorrectionFormulaTrace`, `NoGuardCorrectionFormulaTrace.model`, `noGuardCorrectionFormulaTrace`, `noGuardCorrectionFormulaTrace_model`, `noGuardCorrectionFormulaCounterexample`, `noGuardCorrectionFormulaCounterexample_model`, `noGuardCorrectionFormulaCounterexample_not_exact`, `noGuardCorrectionFormulaCounterexample_toCorrectionFormulaTrace_not_exact`, `kahanNoGuardStepTrace`, `kahanNoGuardStep`, `kahanNoGuardStepTrace_temp`, `kahanNoGuardStepTrace_y`, `kahanNoGuardStepTrace_s`, `kahanNoGuardStepTrace_e`, `kahanNoGuardPrefixState`, `kahanNoGuardTrace`, `fl_kahanNoGuardState`, `fl_kahanNoGuardSum`, `fl_kahanNoGuardCorrection`, `kahanNoGuardCounterexampleModel`, `kahanNoGuardCounterexampleInput`, `fl_kahanNoGuardCounterexampleState_eq`, `fl_kahanNoGuardCounterexampleSum_eq`, `fl_kahanNoGuardCounterexampleCorrection_eq`, `kahanNoGuardCounterexample_exactSum_eq`, `kahanNoGuardCounterexample_relError_eq_one`, `kahanSameSign`, `KahanModifiedNoGuardStepTrace`, `kahanModifiedNoGuardStepTrace`, `kahanModifiedNoGuardStep`, `kahanModifiedNoGuardStepTrace_temp`, `kahanModifiedNoGuardStepTrace_y`, `kahanModifiedNoGuardStepTrace_s`, `kahanModifiedNoGuardStepTrace_f0`, `kahanModifiedNoGuardStepTrace_f`, `kahanModifiedNoGuardStepTrace_e`, `kahanModifiedNoGuardPrefixState`, `kahanModifiedNoGuardTrace`, `fl_kahanModifiedNoGuardState`, `fl_kahanModifiedNoGuardSum`, `fl_kahanModifiedNoGuardCorrection`, `kahanModifiedNoGuardStep_exactWithUnitRoundoff`, `fl_kahanModifiedNoGuardState_exactWithUnitRoundoff`, `fl_kahanModifiedNoGuardSum_exactWithUnitRoundoff`, `fl_kahanModifiedNoGuardCorrection_exactWithUnitRoundoff` | The local no-guard correction-formula trace is closed, including a concrete `u = 1/4`, `a = 1`, `b = -7/8` local model witness with `|a| > |b|` for which `a + b = s + e` is false. The ordinary no-guard Kahan trace is now closed, and the two-term model/input witness proves the full compensated run returns `1/4` with zero correction while the exact sum is `1/8`, so the relative error is exactly one. Kahan's modified correction path is closed as a source-level `NoGuardFPModel` trace, including `f = 0`, the same-sign branch `f = (0.46*s - s) + s`, and `e = ((temp - f) - (s - f)) + y` in the displayed evaluation order. Its exact-arithmetic sanity surface is now closed: the auxiliary same-sign branch cancels in the correction assignment, the final modified state has exact source sum and zero retained correction, the returned sum is exact, and the retained correction is zero. Kahan's machine-dependent guarantee remains open. |
| pp. 95--96, Euler-method example and Figure 4.2 | Compensated summation reduces rounding effects in a numerical Euler experiment. | OPEN/PROSE | N/A | The plotted Fortran/Sun experiment is not formalized. A theorem would require an Euler implementation and experiment/model specification. |
| pp. 96--97, Algorithm 4.3 | Priest doubly compensated summation algorithm and full-precision guarantee when `n < beta^(t-3)`. | PARTIAL | `priestSortedByDecreasingAbs`, `priestStrictlySortedByDecreasingAbs`, `priestSortedByDecreasingAbs_of_strict`, `PriestState`, `PriestStepTrace`, `priestStepTrace`, `priestStepTrace_y`, `priestStepTrace_u`, `priestStepTrace_t`, `priestStepTrace_upsilon`, `priestStepTrace_z`, `priestStepTrace_s`, `priestStepTrace_c`, `priestPrefixState`, `priestTrace`, `fl_priestState`, `fl_priestSum`, `fl_priestCorrection`, `fl_priestState_exactWithUnitRoundoff`, `fl_priestSum_exactWithUnitRoundoff`, `fl_priestCorrection_exactWithUnitRoundoff` | Algorithm 4.3's source-level rounded trace is closed for a supplied decreasing-magnitude input order, and the source's strict decreasing-order precondition now has a theorem bridge to the weak trace predicate. The zero-roundoff sanity surface is also closed: under exact arithmetic, the final state is the exact source sum with zero retained correction, the returned sum is exact, and the retained correction is zero. The full-precision guarantee remains open and needs finite-format assumptions and proof-source acquisition from Priest. |
| pp. 97--98, other methods | Wolfe/Malcolm/Ross accumulator methods and distillation algorithms; Malcolm relative-error order `u`; distillation average runtime comments. | PARTIAL | `AccumulatorState`, `AccumulatorOverflowTest`, `accumulatorCascadeFrom`, `accumulatorCascadeFrom_no_overflow`, `accumulatorCascadeFrom_overflow_to_next`, `accumulatorCascadeFrom_no_next_level`, `accumulatorAddTerm`, `accumulatorPrefixState`, `fl_accumulatorState`, `DecreasingAbsAccumulatorOrder`, `fl_accumulatorFinalSum`, `fl_accumulatorSum`, `fl_accumulatorSum_eq_recursive_final_state`, `fl_accumulatorSum_uses_decreasing_abs_order`, `accumulatorNeverOverflow`, `accumulatorIdentityOrder`, `fl_accumulatorState_neverOverflow_zero_exactWithUnitRoundoff`, `fl_accumulatorState_neverOverflow_of_ne_zero_exactWithUnitRoundoff`, `fl_accumulatorSum_neverOverflow_exactWithUnitRoundoff`, `fl_accumulatorSum_singleLevel_neverOverflow_exactWithUnitRoundoff`, `DistillationState`, `DistillationTrace`, `distillationStateSum`, `distillationInitialState_sum_eq`, `distillationTrace_sum_preserved`, `distillationTrace_finalState_sum_eq`, `distillationTrace_finalState_sum_eq_initial`, `DistillationTrace.terminatesWithinUnitRoundoff`, `distillationTrace_finalComponent_relError_le`, `distillationTrace_finalComponent_abs_error_le` | The source-level accumulator cascade is closed with an abstract machine-dependent overflow predicate, finite accumulator bank, reset-and-carry behavior, and final recursive summation in a supplied decreasing-absolute-value order. The final Malcolm-order surface is explicitly closed: `fl_accumulatorSum_eq_recursive_final_state` identifies the final phase with recursive summation of the accumulator bank in the supplied order, and `fl_accumulatorSum_uses_decreasing_abs_order` records the decreasing-absolute-value order condition. A concrete no-overflow exact-arithmetic sanity path is also closed for any finite accumulator bank: the lowest accumulator contains the exact source sum, every higher accumulator remains zero, and the never-overflow method with identity final order returns the exact source sum. The previous one-level theorem is retained as the scalar-bank specialization. The source-level distillation paragraph is closed as an abstract trace preserving the exact sum and terminating when the final component has relative error at most `u`; `distillationInitialState_sum_eq`, `distillationTrace_finalState_sum_eq`, and `distillationTrace_finalState_sum_eq_initial` expose the initial-to-final exact-sum preservation, `distillationTrace_finalComponent_relError_le` exposes the relative-error guarantee directly, and `distillationTrace_finalComponent_abs_error_le` gives the absolute-error consequence `|z - sum x| <= u * |sum x|` under nonzero exact sum. Malcolm's finite-machine relative-error order-`u` analysis, concrete overflow/interval assumptions, concrete distillation transforms, and average-runtime lower/order claims remain open. |
| pp. 98--99, Section 4.5 and Table 4.1 | Statistical mean-square error estimates for nonnegative inputs under independent zero-mean addition errors. | PARTIAL | `statisticalWeightedRoundingErrorSum`, `StatisticalRoundingErrorModel.expectation_weighted_sum_eq_zero`, `StatisticalRoundingErrorModel.expectation_weighted_sum_sq_eq_sum_weight_sq_second_moments`, `StatisticalRoundingErrorModel.expectation_weighted_sum_sq_le_weight_sq_mul_unit_sq`, `StatisticalRoundingErrorModel.rms_weighted_sum_le_sqrt_weight_sq_mul_unit`, `SumTree.computedInternalSums`, `SumTree.computedInternalSums_length_eq_numAdds`, `SumTree.computedInternalSums_abs_sum_eq_runningErrorBudget`, `SumTree.statisticalRunningErrorContribution`, `SumTree.statisticalRunningErrorContribution_expectation_eq_zero`, `SumTree.statisticalRunningErrorContribution_expectation_sq_eq_sum`, `SumTree.statisticalRunningErrorContribution_expectation_sq_le`, `SumTree.statisticalRunningErrorContribution_rms_le`, `Table41Distribution`, `Table41Method`, `table41MeanSquareConstant`, `table41NExponent`, `table41MeanSquareEstimate`, `table41_recursive_constants_rank_uniform`, `table41_recursive_constants_rank_exponential`, `table41_insertion_constant_lt_pairwise_uniform`, `table41_insertion_constant_lt_pairwise_exponential`, `table41_recursive_exponents_eq_three`, `table41_insertion_pairwise_exponents_eq_two`, `table41MeanSquareScale_pos`, `table41_recursive_estimates_rank_uniform`, `table41_recursive_estimates_rank_exponential`, `table41_insertion_estimate_lt_pairwise_uniform`, `table41_insertion_estimate_lt_pairwise_exponential` | The generic finite-probability kernel is now closed: deterministic intermediate-sum weights multiplying zero-mean pairwise-uncorrelated addition errors have zero mean, mean square equal to the weighted sum of local second moments, and RMS at most `sqrt (sum_i w_i^2) * u` when each local second moment is at most `u^2`. The Algorithm 4.1 connection is also closed: `SumTree.computedInternalSums` flattens the actual computed internal sums `T_hat_i`, its length equals the number of additions, its absolute-value sum equals `SumTree.runningErrorBudget`, and `SumTree.statisticalRunningErrorContribution_*` applies the statistical kernel to those exact tree weights. The displayed Table 4.1 constants and `n` exponents are encoded exactly, and the immediate qualitative conclusions from the printed table are checked: recursive constants rank increasing < random < decreasing for both input distributions, insertion has a smaller displayed constant than pairwise for both distributions, recursive columns have `n^3` scaling, and insertion/pairwise have `n^2` scaling. The same rankings are now closed for the full displayed mean-square estimate expression whenever the common scale `mu^2 * n^k * sigma^2` is positive: `table41_recursive_estimates_rank_uniform`, `table41_recursive_estimates_rank_exponential`, `table41_insertion_estimate_lt_pairwise_uniform`, and `table41_insertion_estimate_lt_pairwise_exponential` lift the constant comparisons to the full estimate. Remaining target: derive the Robertazzi--Schwartz constants from their distributional assumptions for the five methods. |
| p. 99, Section 4.6 advice item 1 | Higher-precision recursive summation plus final rounding has a displayed error form; Priest decreasing-order higher-precision theorem; doubly compensated summation gives small relative error. | PARTIAL | `HigherPrecisionRecursiveSumTrace`, `higherPrecisionRecursiveSumTrace`, `higherPrecisionRecursiveSumTrace_highSum`, `higherPrecisionRecursiveSumTrace_roundedSum`, `fl_higherPrecisionRecursiveSum`, `fl_higherPrecisionRecursiveSum_eq_round_highSum`, `fl_higherPrecisionRecursiveSum_exactWithUnitRoundoff_id`, `fl_higherPrecisionRecursiveSum_abs_error_le_of_high_bound`, `fl_higherPrecisionRecursiveSum_abs_error_le_nu_sq`, `fl_higherPrecisionRecursiveSum_abs_error_le_gamma`, `fl_higherPrecisionRecursiveSum_relError_le_of_high_bound_oneSigned`, `fl_higherPrecisionRecursiveSum_relError_le_gamma_oneSigned`, `SimulatesHigherPrecision` | The source-level trace "recursive summation in higher precision, then round to working precision" is closed with an explicit final rounding map and the existing precision relation. The zero-roundoff identity-final-rounding sanity surface is also closed: exact high-precision recursive summation followed by identity final rounding returns the exact source sum. The displayed mixed-precision two-term error composition is closed: a final working-precision relative rounding bound plus a high-precision recursive-stage bound gives `u*|high sum| + eps*sum |x_i|`, with a checked `n*u^2` specialization and a gamma-form theorem derived from the existing recursive-summation bound. The one-signed relative-error lift is now closed as well: if the exact sum is nonzero, the high-stage absolute error is at most `eps*sum |x_i|`, and final rounding has relative radius `u`, then the final relative error is at most `u*(1+eps)+eps`; the gamma specialization instantiates `eps = gamma highFp (n-1)`. Priest's decreasing-order higher-precision theorem and the doubly compensated relative-error guarantee remain open. |
| p. 99, Section 4.6 advice items 2--4 | Pairwise and compensated methods are attractive for large `n`; one-signed data have relative error at most `nu`, compensated summation can be perfectly relatively accurate, and decreasing order is attractive under heavy cancellation. | PARTIAL | `SumTree.forward_error_n_minus_one`, `SumTree.relError_le_gamma_n_minus_one_of_oneSigned`, `gamma_le_two_mul_n_u_of_nu_le_half`, `SumTree.relError_le_two_mul_n_minus_one_u_of_oneSigned`, `gamma_pred_le_n_mul_u_of_n_mul_pred_u_le_one`, `SumTree.relError_le_n_mul_u_of_oneSigned`, `recursiveSum_relError_le_gamma_of_oneSigned`, `recursiveSum_relError_le_n_mul_u_of_oneSigned`, `pairwiseSum_relError_le_gamma_of_oneSigned`, `pairwiseSum_relError_le_pow_two_mul_u_of_oneSigned`, `pairwiseCarrySum_relError_le_gamma_of_oneSigned`, `pairwiseCarrySum_relError_le_n_mul_u_of_oneSigned`, `clog2PairwiseSum_relError_le_gamma_of_oneSigned`, `pairwiseCarryTree_depth_le_linear`, `fl_higherPrecisionRecursiveSum_relError_le_of_high_bound_oneSigned`, `fl_higherPrecisionRecursiveSum_relError_le_gamma_oneSigned`, `SumTree.balancedTree_forward_error`, `HeavyCancellationAtLeast`, `relError_pos_of_ne_exact`, `relError_le_of_abs_sub_le_mul_abs`, `heavyCancellation_postCancellation_bound_beats_competitor`, `heavyCancellation_exact_result_beats_inexact_result`, `heavyCancellation_exact_result_beats_zero_result`, `p91Increasing_heavyCancellationAtLeast`, `p91Psum_heavyCancellationAtLeast`, `p91Decreasing_heavyCancellationAtLeast`, `p91_decreasing_postCancellation_bound_beats_increasing`, `p91_decreasing_postCancellation_bound_beats_psum` | Pairwise and general worst-case gamma bounds are closed. The pairwise logarithmic-depth comparison is now explicit: `pairwiseCarryTree_depth_le_linear` proves the source-shaped carry-forward pairwise depth `ceil(log2 n)` is no larger than the generic `n - 1` depth for nonempty inputs. The one-signed absolute-to-relative reduction is closed in exact `gamma` form for generic Algorithm 4.1 trees, recursive summation, pairwise summation, and the higher-precision recursive-sum-then-round trace under the standard nonzero exact-sum condition. A small-`u` linearized version is closed for generic Algorithm 4.1 trees: if `(n-1)u <= 1/2`, the one-signed relative error is at most `2(n-1)u`. The source-shaped `nu` wording is now closed for nonempty generic Algorithm 4.1 trees by `SumTree.relError_le_n_mul_u_of_oneSigned`: under `gammaValid (n-1)` and the explicit smallness condition `n*(n-1)*u <= 1`, one-signed data with nonzero exact sum have relative error at most `n*u`. Direct method-level wrappers are also closed for recursive summation (`recursiveSum_relError_le_n_mul_u_of_oneSigned`), power-of-two pairwise summation (`pairwiseSum_relError_le_pow_two_mul_u_of_oneSigned`, from the sharper logarithmic gamma bound), and source-shaped carry-forward pairwise summation (`pairwiseCarrySum_relError_le_n_mul_u_of_oneSigned`). The higher-precision method-choice relative surface is closed conditionally by `fl_higherPrecisionRecursiveSum_relError_le_of_high_bound_oneSigned` and `fl_higherPrecisionRecursiveSum_relError_le_gamma_oneSigned`. The source's heavy-cancellation condition is now represented by `HeavyCancellationAtLeast`; `heavyCancellation_exact_result_beats_inexact_result` proves the general comparison surface that, under a shared nonzero exact sum and explicit heavy-cancellation regime, an exact computed result has smaller relative error than any inexact competitor; the zero-collapse theorem remains as the p. 91 special case. The checkable post-cancellation comparison is closed by `relError_le_of_abs_sub_le_mul_abs` and `heavyCancellation_postCancellation_bound_beats_competitor`, and the p. 91 increasing/Psum collapses are instantiated by `p91_decreasing_postCancellation_bound_beats_increasing` and `p91_decreasing_postCancellation_bound_beats_psum`. The p. 91 example proves the exact amplification factor `1 + 6M` while showing the decreasing ordering can be exact where increasing/Psum fail. Compensated perfect-relative-accuracy, arbitrary-`FPModel` computed-bound insertion-minimization, and deriving concrete post-cancellation certificates from a general decreasing-order finite-format computation remain open. |
| p. 100, Section 4.7 | Notes and references for summation, compensated summation, pairwise summation, serial pairwise storage, and quadrature/ODE contexts. | PROSE | N/A | Bibliographic and historical notes only; proof-source obligations are tracked in `docs/CHAPTER04_PROOF_SOURCE_LEDGER.md` where they support theorem-bearing rows. |
| p. 100, Problem 4.1 | Define and evaluate a condition number `C(x)` for `S_n(x) = sum_i x_i`, and characterize when it equals `1`. | CLOSED | `SummationComponentwisePerturbation`, `summationConditionNumber`, `summationConditionNumber_eq`, `summationComponentwisePerturbation_abs_error_le`, `summationComponentwisePerturbation_rel_error_le_condition`, `summationConditionNumber_attained`, `one_le_summationConditionNumber`, `summationConditionNumber_eq_one_of_oneSigned`, `summationConditionNumber_eq_one_iff_oneSigned`, `sum_abs_eq_abs_sum_iff_oneSigned` | The componentwise relative perturbation model is now explicit. Lean proves the sharp closed form `C(x) = (sum_i |x_i|)/|sum_i x_i|` by an upper bound plus a sign-aligned attaining perturbation, proves `C(x) >= 1` whenever the exact sum is nonzero, and proves that `C(x) = 1` exactly for one-signed/no-cancellation input data. |
| pp. 100--101, Problem 4.2 | Wilkinson attainability exercise: show recursive-summation bounds (4.3) and (4.4) are nearly attainable for the displayed powers-of-two input family. | PARTIAL | `wilkinsonProblem42BlockValue`, `wilkinsonProblem42Input`, `wilkinsonProblem42ExactSum`, `wilkinsonProblem42Defect`, `wilkinsonProblem42Vector`, `finiteRoundToEvenRecursiveSum`, `finiteRoundToEvenListSum`, `finiteRoundToEvenRecursiveSum_eq_listSum`, `wilkinsonProblem42Input_length`, `wilkinsonProblem42Input_sum_eq`, `wilkinsonProblem42Input_zero`, `wilkinsonProblem42Input_succ`, `wilkinsonProblem42Vector_toList`, `wilkinsonProblem42Vector_sum_eq`, `wilkinsonProblem42ExactSum_add_defect`, `wilkinsonProblem42Defect_nonneg`, `wilkinsonProblem42Defect_closed_form`, `wilkinsonProblem42ExactSum_le_pow`, `wilkinsonProblem42_first_order_bound_le_three_defect_plus_u`, `wilkinsonProblem42_gamma_bound_le_three_defect_plus_u_div`, `wilkinsonProblem42_abs_error_eq_defect_of_recursiveSum_eq_pow`, `wilkinsonProblem42_recursiveSum_eq_pow_zero`, `wilkinsonProblem42BlockValue_ieeeDouble_finiteSystem`, `wilkinsonProblem42Input_ieeeDouble_all_finiteSystem`, `wilkinsonProblem42Vector_ieeeDouble_finiteSystem`, `wilkinsonProblem42_ieeeDouble_sameBinade_add_rounds_to_nat`, `wilkinsonProblem42_ieeeDouble_block_boundary_add_rounds_to_pow`, `wilkinsonProblem42_ieeeDouble_block_prefix_accumulator`, `wilkinsonProblem42_ieeeDouble_block_rounds_pow_to_next_pow`, `wilkinsonProblem42_ieeeDouble_listRecursiveSum_eq_pow`, `wilkinsonProblem42_ieeeDouble_finiteRecursiveSum_eq_pow`, `wilkinsonProblem42_ieeeDouble_abs_error_eq_defect`, `wilkinsonProblem42_ieeeDouble_abs_error_closed_form`, `wilkinsonProblem42_unit_roundoff_le_defect_of_pos`, `wilkinsonProblem42_ieeeDouble_first_order_bound_le_three_abs_error_plus_u`, `wilkinsonProblem42_ieeeDouble_first_order_bound_le_four_abs_error`, `wilkinsonProblem42_ieeeDouble_gamma_bound_le_three_abs_error_plus_u_div`, `wilkinsonProblem42_ieeeDouble_gamma_bound_le_eight_abs_error`, `wilkinsonProblem42_ieeeDouble_first_block_rounds_to_two`, `wilkinsonProblem42_ieeeDouble_finiteRecursiveSum_eq_pow_one`, `wilkinsonProblem42_ieeeDouble_finiteRecursiveSum_eq_pow_two`, `wilkinsonProblem42BlockValue_nonneg_of_le`, `wilkinsonProblem42Input_nonneg_of_le`, `wilkinsonProblem42Vector_nonneg_of_le`, `wilkinsonProblem42Vector_oneSigned_of_le`, `wilkinsonProblem42Vector_sum_abs_eq`, `wilkinsonProblem42ExactSum_pos_of_le`, `wilkinsonProblem42ExactSum_ne_zero_of_le`, `wilkinsonProblem42_recursiveSum_running_error_bound`, `wilkinsonProblem42_recursiveSum_forward_error_bound`, `wilkinsonProblem42_recursiveSum_relError_le_gamma`, `wilkinsonProblem42_recursiveSum_relError_le_pow_mul_u` | The generic recursive and tree bounds are closed, and Wilkinson's displayed powers-of-two input family is formalized exactly at the source-list and defect-algebra level. For the concrete IEEE-double instantiation `t = 53`, Lean proves every displayed input is finite representable, the reusable same-binade and power-boundary rounding steps, the complete block prefix invariant, the full block map `2^j -> 2^(j+1)`, and the arbitrary list and `Fin` finite round-to-even traces returning `2^r` for every `r <= 52`. Lean also proves the realized absolute error equals the defect, the realized-error closed form, first-order near-attainment within factor `4` for positive `r`, and exact-gamma near-attainment within factor `8` under the explicit denominator condition `2*(2^r-1)*2^-53 <= 1`. Under the source regime `r <= t + 1`, Lean proves all entries are nonnegative/one-signed, the recursive-summation absolute-value majorant collapses to the exact Wilkinson sum, the exact source sum is positive, and the recursive-summation running-error bound (4.3), a priori bound (4.4), gamma-relative bound, and powers-of-two `n*u` corollary all specialize to the Wilkinson vector without a separate nonzero-denominator hypothesis. Remaining scope: the paper phrases the construction for generic `t`-digit base-2 arithmetic; the repository now closes the IEEE-double route, while a fully generic arbitrary-precision route is not claimed. The resolved bottleneck and optional generic lift are tracked in `docs/CHAPTER04_P42_WILKINSON_ATTAINABILITY_BOTTLENECK.md`. |
| p. 101, Problem 4.3 | Recursive summation in natural order: derive the displayed `theta_k/gamma_k` representation, the weighted error bound, and the ordering minimizing that bound. | CLOSED | `sumSuffixErrorProduct_exists_theta_le_gamma`, `recursiveSum_problem43_variableGamma`, `recursiveSum_problem43_abs_error_bound`, `recursiveSumProblem43GammaWeight`, `recursiveSumProblem43WeightedAbsBound`, `recursiveSumProblem43WeightedAbsBound_eq_display`, `recursiveSum_problem43_abs_error_bound_weighted`, `weighted_abs_pair_exchange_le`, `recursiveSum_problem43_tail_gamma_weight_mono`, `recursiveSum_problem43_leading_gamma_weight_ge_tail`, `recursiveSum_problem43_tail_pair_exchange_le`, `recursiveSum_problem43_gamma_weight_mono`, `recursiveSum_problem43_antivary_abs_gammaWeight_of_increasingAbs`, `recursiveSum_problem43_increasingAbs_weightedBound_le_perm`, `recursiveExactPrefixBudget`, `increasingAbsSort_recursiveExactPrefixBudget_le`, `psumOrder_recursiveExactPrefixBudget_le` | The exact displayed representation is closed for `m + 2` inputs: `(x_1+x_2)` carries a `theta` bounded by `gamma_{m+1}`, each later term carries the suffix-indexed `gamma_{m-j}`, and the stated weighted absolute-error bound follows. The displayed right-hand side is also packaged as `recursiveSumProblem43WeightedAbsBound`. The ordering answer is closed in global finite-permutation form: the indexed `gamma` weights are nonincreasing, the leading block has the largest weight, the adjacent-exchange certificate holds, and `recursiveSum_problem43_increasingAbs_weightedBound_le_perm` proves that once data are arranged by nondecreasing absolute value every finite reordering has weighted bound at least as large. |
| p. 101, Problem 4.4 | For `{1,2,3,4,M,-M}` with `fl(10+M)=M`, determine all possible recursive-summation outputs. | CLOSED | `Problem44Term`, `Problem44Accumulator`, `problem44Step`, `problem44Source`, `problem44Eval`, `problem44Output`, `problem44Source_exact_sum`, `problem44PossibleOutputs`, `problem44PossibleOutputs_eq_Icc`, `problem44Output_mem_Icc_of_perm`, `problem44Every_Icc_output_attained`, `problem44_outputs_exactly_Icc` | A source-shaped absorbing-large-`M` recursive-summation model is now formalized: small integer additions are exact, small accumulated parts are absorbed when a large term is active, and `M` cancels exactly with `-M`. Exhaustive enumeration over all six-term permutations proves that the possible outputs are exactly `0,1,...,10`, and that every value in this interval is attained. The exact real source multiset sum is separately proved to be `10`. |
| p. 101, Problem 4.5 | Analyze the pros and cons of the "+/-" method: sum positive and nonpositive terms separately, then add the two sums. | CLOSED | `positivePart`, `nonpositivePart`, `plusMinusPositive`, `plusMinusNonpositive`, `plusMinusExactPositive`, `plusMinusExactNonpositive`, `plusMinusExactNonpositive_add_positive`, `plusMinusPositive_oneSigned`, `plusMinusNonpositive_oneSigned`, `plusMinusPositive_conditionNumber_eq_one`, `plusMinusNonpositive_conditionNumber_eq_one`, `plusMinus_final_add_error_bound`, `fl_plusMinusRecursiveSum`, `fl_plusMinusRecursiveSum_error_bound`, `fl_plusMinusRecursiveSum_relError_bound` | The theorem surface makes the prose comparison precise. The exact split preserves the source sum. Each separated input is one-signed, so its summation condition number is one whenever the corresponding exact partial sum is nonzero. The abstract final-add theorem accepts any supplied method for the two separated sums, while `fl_plusMinusRecursiveSum_error_bound` instantiates recursive summation and exposes the two stable separated-sum error terms plus the final rounded-add term. The relative-error corollary records the disadvantage: if the final positive and nonpositive sums nearly cancel, the denominator `|sum_i x_i|` can be small. |
| p. 101, Problem 4.6 | Aitken extrapolation denominator `x_{i+2}-2x_{i+1}+x_i`: compare three algebraically equivalent evaluation orders. | CLOSED | `aitkenDenominatorA`, `aitkenDenominatorB`, `aitkenDenominatorC`, `aitkenDenominatorA_eq_B`, `aitkenDenominatorC_eq_B`, `fl_aitkenDenominatorA`, `fl_aitkenDenominatorB`, `fl_aitkenDenominatorC`, `aitkenDenominatorAMajorant`, `aitkenDenominatorBMajorant`, `aitkenDenominatorCMajorant`, `aitkenDenominatorBMajorant_add_const`, `aitkenDenominatorAMajorant_add_const`, `aitkenDenominatorCMajorant_add_const`, `fl_aitkenDenominatorA_backward_error`, `fl_aitkenDenominatorA_error_bound`, `fl_aitkenDenominatorB_backward_error`, `fl_aitkenDenominatorB_error_bound`, `fl_aitkenDenominatorC_backward_error`, `fl_aitkenDenominatorC_error_bound`, `aitkenDenominator_recommended_route_b` | The three exact denominator expressions are proved algebraically identical. At the rounded standard-model parenthesization level, with multiplication by `2` treated as exact, Lean derives absolute-error bounds for all three routes and a backward-error form for the first-difference route `(x_{i+2}-x_{i+1})-(x_{i+1}-x_i)`. The first-difference route is the formal recommendation: its majorant depends only on successive differences and is invariant under adding the common limiting offset, while the route (a) and route (c) majorants retain that offset. A concrete machine model that rounds multiplication by `2` would add an extra finite-format side condition for routes (a) and (c), not weaken the recommendation. |
| pp. 101--102, Problem 4.7 | Analyze `S_n = log (prod_i exp(x_i))` as a method for evaluating a sum. | CLOSED | `logExpProductExact`, `logExpProductExact_eq_sum`, `LogExpProductTrace`, `logExpProductTrace`, `logExpProduct_product_perturbation`, `logExpProduct_final_error_eq`, `logExpProduct_final_abs_error_eq`, `logExpProduct_final_relError_eq`, `logExpProduct_composed_error` | The exact identity `log (prod_i exp x_i) = sum_i x_i` is proved. The rounded-method analysis is closed at the real-valued perturbation surface: relative errors in the exponential stage plus a product-stage `gamma_{n-1}` error compose to a single product perturbation bounded by `gamma_{n+(n-1)}`, and the final log stage has absolute error `|log(1+theta)+eta|` and relative-error denominator `|sum_i x_i|`. The explicit positivity side condition on `1+theta` records the finite no-overflow/no-underflow/no-sign-flip requirement for the logarithm input. |
| pp. 101--102, Problem 4.8 | Compare three ways to form equally spaced grid points: recurrence `x_i=x_{i-1}+h`, direct `a+i h`, and convex combination `a(1-i/n)+(i/n)b`. | CLOSED | `gridPointExact`, `gridPointFromStep`, `gridPointConvex`, `gridPointConvex_eq_exact`, `gridPointFromStep_error_eq`, `fl_gridRecurrence`, `fl_gridDirect`, `fl_gridConvex`, `fl_gridRecurrence_storedStep_error_bound`, `fl_gridRecurrence_error_bound`, `fl_gridDirect_storedStep_error_bound`, `fl_gridDirect_error_bound`, `fl_gridConvex_error_bound` | The three source formulas are formalized. Lean proves the convex expression is exactly the ideal grid point, and proves the stored-step representation identity exposing the term `i * |hhat - (b-a)/n|`. The rounded recurrence and direct routes carry both their standard-model rounding terms and the stored-step representation term, while the rounded convex route has only the local multiply/add rounding terms and no stored-step amplification, matching the source's point that `a` and `b`, but not necessarily `h`, are directly represented. |
| p. 102, Problem 4.9 | Priest research problem: determine the smallest `n` for which decreasing-absolute-value compensated summation can have large relative error; includes the displayed IEEE single counterexample family. | OPEN | N/A | The local Priest and Kahan traces are present, but the three-term `O(u)` theorem, the displayed single-precision failure trace, and the smallest-`n` research conclusion are not formalized. |

Current p. 91 exact-arithmetic insertion-optimality status: the explicit weighted-depth
rearrangement and contraction surface now includes maximum-depth sibling
existence via `InsertionScheduleTree.exists_deepest_sibling_leaf_pair` and
all-entry depth control via
`InsertionScheduleTree.leafDepthWeights_depth_le_maxLeafDepth`, plus
adjacent and separated two-position exchange lemmas, respectively
`InsertionScheduleTree.weightedDepthPairsCost_pair_exchange_le` and
`InsertionScheduleTree.weightedDepthPairsCost_pair_exchange_separated_le`.
The one-slot permutation/context-minimum variants needed for overlap cases are
closed by
`InsertionScheduleTree.weightedDepthPairsCost_pair_exchange_separated_of_perm_le_and_weights_perm`
and
`InsertionScheduleTree.weightedDepthPairsCost_pair_exchange_of_context_min_le_and_weights_perm`.
The no-op pair-list branch is closed by
`InsertionScheduleTree.weightedDepthPairsCost_of_perm_le_and_weights_perm`.
The two-slot deepest-pair exchange core is closed by
`InsertionScheduleTree.weightedDepthPairsCost_two_pair_exchange_separated_le`
and its `List.Perm` wrapper
`InsertionScheduleTree.weightedDepthPairsCost_two_pair_exchange_separated_of_perm_le`;
the located two-smallest context handoff is closed by
`InsertionScheduleTree.weightedDepthPairsCost_two_pair_exchange_of_context_min_le`,
and the same handoff bundled with leaf-weight multiset preservation is closed
by
`InsertionScheduleTree.weightedDepthPairsCost_two_pair_exchange_of_context_min_le_and_weights_perm`.
The nondegenerate branch combining a displayed deepest pair with a finite
two-smallest decomposition whose selected entries are outside that pair is
closed by
`InsertionScheduleTree.weightedDepthPairsCost_two_pair_exchange_of_two_smallest_decomposition_le_and_weights_perm`.
The overlap branches where the first two-smallest entry is already the left or
right member of the deepest sibling pair are closed by
`InsertionScheduleTree.weightedDepthPairsCost_pair_exchange_of_left_deepest_two_smallest_decomposition_le_and_weights_perm`
and
`InsertionScheduleTree.weightedDepthPairsCost_pair_exchange_of_right_deepest_two_smallest_decomposition_le_and_weights_perm`.
The mirror branches where the second two-smallest entry is already the left or
right deepest sibling are closed by
`InsertionScheduleTree.weightedDepthPairsCost_pair_exchange_of_left_deepest_second_two_smallest_decomposition_le_and_weights_perm`
and
`InsertionScheduleTree.weightedDepthPairsCost_pair_exchange_of_right_deepest_second_two_smallest_decomposition_le_and_weights_perm`.
The explicit branch dispatcher that packages the no-op, nonoverlap, and all
one-slot overlap cases is closed by
`InsertionScheduleTree.TwoSmallestDeepestExchangeBranch` and
`InsertionScheduleTree.weightedDepthPairsCost_two_smallest_deepest_exchange_branch_le_and_weights_perm`.
The conditional bridge from a dispatcher-produced explicit pair list back to a
realized schedule tree is closed by
`InsertionScheduleTree.weightedLeafDepthCost_two_smallest_deepest_exchange_branch_realized_le_and_leaves_perm`.
Same-shape relabeling is closed by
`InsertionScheduleTree.relabelLeaves_leaves_eq`,
`InsertionScheduleTree.relabelLeaves_leafDepthWeights_eq_zip`, and
`InsertionScheduleTree.exists_relabelLeaves_leafDepthWeights_eq_of_depths_eq`;
the same-depth dispatcher output to actual schedule tree bridge is closed by
`InsertionScheduleTree.exists_relabelLeaves_for_two_smallest_deepest_exchange_branch_of_depths_eq`.
The contraction-aware same-depth dispatcher bridge is closed by
`InsertionScheduleTree.exists_relabelLeaves_contract_for_two_smallest_deepest_exchange_branch_of_context_lengths`,
with branch surfaces for nonoverlap, one-slot overlap, and no-op cases closed
by the `exists_relabelLeaves_contract_for_*_contracted_pair` family and
`InsertionScheduleTree.exists_relabelLeaves_contract_for_deepest_pair_noop`.
The contraction-aware nonoverlap occurrence classifiers are closed by
`InsertionScheduleTree.exists_relabelLeaves_contract_for_first_before_contracted_pair_nonoverlap_anywhere`
and
`InsertionScheduleTree.exists_relabelLeaves_contract_for_first_after_contracted_pair_nonoverlap_anywhere`;
the first-selected-outside classifiers allowing the second selected entry to
be either nonoverlapping or one of the old contracted siblings are closed by
`InsertionScheduleTree.exists_relabelLeaves_contract_for_first_before_contracted_pair_anywhere`
and
`InsertionScheduleTree.exists_relabelLeaves_contract_for_first_after_contracted_pair_anywhere`.
The first-selected-inside contraction classifiers allowing the second selected
entry to be before the old pair, after the old pair, or the other old sibling
are closed by
`InsertionScheduleTree.exists_relabelLeaves_contract_for_left_deepest_first_two_smallest_anywhere`
and
`InsertionScheduleTree.exists_relabelLeaves_contract_for_right_deepest_first_two_smallest_anywhere`.
These return an actual normalized `SiblingLeafContract` in either sibling
orientation, matching the realized overlap branch.
The fixed-context arbitrary occurrence dispatcher combinator is closed by
`InsertionScheduleTree.exists_relabelLeaves_contract_for_two_smallest_deepest_pair_anywhere_of_occurrence_classifiers`;
it preserves one shared old sibling-pair context and combines the
selected-relative-to-adjacent-pair split once four fixed-context occurrence
continuations are supplied.
The branch-specific same-depth tree assembly adapters for the no-op,
nonoverlap, four after-pair overlap cases, and four before-pair overlap cases
are closed by
`InsertionScheduleTree.exists_tree_for_deepest_pair_noop_eq`,
`InsertionScheduleTree.exists_tree_for_two_pair_exchange_of_two_smallest_decomposition_eq`,
`InsertionScheduleTree.exists_tree_for_two_pair_exchange_reverse_of_two_smallest_decomposition_eq`,
`InsertionScheduleTree.exists_tree_for_two_pair_exchange_before_deepest_of_two_smallest_decomposition_eq`,
`InsertionScheduleTree.exists_tree_for_two_pair_exchange_reverse_before_deepest_of_two_smallest_decomposition_eq`,
`InsertionScheduleTree.exists_tree_for_two_pair_exchange_around_deepest_of_two_smallest_decomposition_eq`,
`InsertionScheduleTree.exists_tree_for_two_pair_exchange_reverse_around_deepest_of_two_smallest_decomposition_eq`,
`InsertionScheduleTree.exists_tree_for_left_deepest_two_smallest_decomposition_eq`,
`InsertionScheduleTree.exists_tree_for_right_deepest_two_smallest_decomposition_eq`,
`InsertionScheduleTree.exists_tree_for_left_deepest_second_two_smallest_decomposition_eq`,
and
`InsertionScheduleTree.exists_tree_for_right_deepest_second_two_smallest_decomposition_eq`;
the before-pair overlap variants are closed by
`InsertionScheduleTree.exists_tree_for_left_deepest_two_smallest_before_deepest_decomposition_eq`,
`InsertionScheduleTree.exists_tree_for_right_deepest_two_smallest_before_deepest_decomposition_eq`,
`InsertionScheduleTree.exists_tree_for_left_deepest_second_two_smallest_before_deepest_decomposition_eq`,
and
`InsertionScheduleTree.exists_tree_for_right_deepest_second_two_smallest_before_deepest_decomposition_eq`.
The finite two-smallest locator is closed by
`InsertionScheduleTree.exists_two_smallest_weight_decomposition` and
`InsertionScheduleTree.exists_two_smallest_weight_decomposition_components`.
The finite occurrence locators needed by the arbitrary branch classifier are
closed by
`InsertionScheduleTree.exists_selected_relative_to_adjacent_pair` and
`InsertionScheduleTree.exists_two_selected_slots_of_perm_cons_cons`.  The
nonoverlap second-position splits for the cases where the first selected
occurrence is before or after the displayed adjacent pair are closed by
`InsertionScheduleTree.exists_second_position_of_first_before_adjacent_pair`
and
`InsertionScheduleTree.exists_second_position_of_first_after_adjacent_pair`;
the combined nonoverlap occurrence-to-tree classifiers are closed by
`InsertionScheduleTree.exists_tree_for_first_before_deepest_two_smallest_nonoverlap_anywhere`
and
`InsertionScheduleTree.exists_tree_for_first_after_deepest_two_smallest_nonoverlap_anywhere`;
the first-selected-outside classifiers allowing the second selected entry to be
either nonoverlapping or one of the deepest siblings are closed by
`InsertionScheduleTree.exists_tree_for_first_before_deepest_two_smallest_anywhere`
and
`InsertionScheduleTree.exists_tree_for_first_after_deepest_two_smallest_anywhere`;
the first-selected-inside classifiers allowing the second selected entry to be
before the pair, after the pair, or the other deepest sibling are closed by
`InsertionScheduleTree.exists_tree_for_left_deepest_first_two_smallest_anywhere`
and
`InsertionScheduleTree.exists_tree_for_right_deepest_first_two_smallest_anywhere`.
The arbitrary displayed-pair classifier combining these four occurrence
orientations with the deepest sibling pair is closed by
`InsertionScheduleTree.exists_tree_for_two_smallest_deepest_pair_anywhere`;
its contraction-ready witness form, which additionally displays the two
selected smallest weights as an adjacent deepest pair in either sibling
orientation, is closed by
`InsertionScheduleTree.exists_tree_for_two_smallest_deepest_pair_anywhere_pair_witness`;
the tree-level placement theorem for arbitrary nontrivial schedules is closed
by
`InsertionScheduleTree.exists_tree_with_two_smallest_at_deepest_pair`.
It also includes sibling contraction identities
`InsertionScheduleTree.weightedLeafDepthCost_node_eq_children_at_depth_add_exactEval`,
`InsertionScheduleTree.weightedLeafDepthCost_node_leaf_leaf_eq_contract`, and
`InsertionScheduleTree.weightedDepthPairsCost_pair_contract_eq`, plus the
structural contraction relation
`InsertionScheduleTree.SiblingLeafContract` and its exact-evaluation,
leaf-count, leaf-context, and weighted-cost facts
`InsertionScheduleTree.SiblingLeafContract.exactEval_eq`,
`InsertionScheduleTree.SiblingLeafContract.leafCount_eq_succ`,
`InsertionScheduleTree.SiblingLeafContract.contracted_leafCount_lt`,
`InsertionScheduleTree.SiblingLeafContract.exists_leaves_context`,
`InsertionScheduleTree.SiblingLeafContract.exists_leafDepthWeights_context`,
`InsertionScheduleTree.SiblingLeafContract.relabelLeaves_contract_of_context_lengths`,
`InsertionScheduleTree.SiblingLeafContract.leaves_perm_of_contracted_perm`,
`InsertionScheduleTree.SiblingLeafContract.contracted_perm_of_leaves_perm`,
`InsertionScheduleTree.SiblingLeafContract.exists_expansion_of_mem`,
`InsertionScheduleTree.SiblingLeafContract.contracted_leaves_nonnegative`, and
`InsertionScheduleTree.SiblingLeafContract.weightedLeafDepthCost_eq`; an
actual maximum-depth sibling contraction, paired with its explicit deepest-pair
display and cost/leaf-count facts, is closed by
`InsertionScheduleTree.exists_deepest_sibling_leaf_contract`, and
`InsertionScheduleTree.exists_deepest_sibling_leaf_contract_with_parent_context`,
`InsertionScheduleTree.exists_deepest_sibling_leaf_contract_with_relabel_parent_context`,
and `InsertionScheduleTree.exists_deepest_sibling_leaf_contract_with_branch_bridge`
provide the parent-depth, same-length relabel, and branch-bridge forms used by
the contraction normalizer; `InsertionScheduleTree.exists_deepest_sibling_leaf_contract_with_leaf_context`
adds the corresponding plain leaf-list context.  The existential Huffman
induction is closed by
`InsertionScheduleTree.exists_pair_decomposition_of_weights_perm_cons_cons`,
`InsertionScheduleTree.exists_relabelLeaves_contract_for_two_smallest_deepest_pair_anywhere_with_induction_data_of_tree`,
`InsertionScheduleTree.GreedyInsertionTree`,
`InsertionScheduleTree.exists_greedyInsertionTree_weightedLeafDepthCost_le`,
`InsertionScheduleTree.exists_greedyInsertionTree_exactMergeCost_le`,
`InsertionScheduleTree.GreedyInsertionTree.weightedLeafDepthCost_le`,
and `InsertionScheduleTree.GreedyInsertionTree.exactMergeCost_le`.
The arbitrary Algorithm 4.1 materialization bridge is closed by
`SumTree.toInsertionScheduleTree`, `SumTree.toInsertionScheduleTree_eval`,
`SumTree.toInsertionScheduleTree_exactEval`,
`SumTree.toInsertionScheduleTree_leafCount`,
`SumTree.toInsertionScheduleTree_leaves_nonnegative`,
`SumTree.eval_exactWithUnitRoundoff`,
`SumTree.runningErrorBudget_exactWithUnitRoundoff_eq_toInsertionScheduleTree_exactMergeCost`, and
`SumTree.runningErrorBudget_exactWithUnitRoundoff_eq_weightedLeafDepthCost_of_nonnegative`.
The concrete source-level exact-arithmetic insertion trace and Algorithm 4.1
comparison are closed by
`insertionScheduleAfter_full_greedy_exactWithUnitRoundoff_of_ne_nil`,
`fl_insertionSumList_has_greedy_schedule_exactWithUnitRoundoff_of_ne_nil`, and
`fl_insertionSumList_exactWithUnitRoundoff_greedy_runningErrorBudget_le`.
The remaining route choice is whether to add an arbitrary-`FPModel`
computed-intermediate theorem with stronger model/order assumptions, or to
keep p. 91's theorem-bearing surface explicitly exact-arithmetic.  The active
dependency checklist is maintained in
`docs/CHAPTER04_P91_INSERTION_OPTIMALITY_BOTTLENECK.md`.

## Current Closed Chapter 4 Lean Names

- `fl_recursiveSum`, `recursiveSum_backward_error`,
  `fl_recursiveSum_exactWithUnitRoundoff`,
  `recursiveSum_forward_error_bound`,
  `recursiveSum_forward_error_bound_oneSigned`,
  `recursiveSum_relError_le_gamma_of_oneSigned`,
  `recursiveSum_running_error_bound`
- `HigherPrecisionRecursiveSumTrace`, `higherPrecisionRecursiveSumTrace`,
  `higherPrecisionRecursiveSumTrace_highSum`,
  `higherPrecisionRecursiveSumTrace_roundedSum`,
  `fl_higherPrecisionRecursiveSum`,
  `fl_higherPrecisionRecursiveSum_eq_round_highSum`,
  `fl_higherPrecisionRecursiveSum_exactWithUnitRoundoff_id`,
  `fl_higherPrecisionRecursiveSum_abs_error_le_of_high_bound`,
  `fl_higherPrecisionRecursiveSum_abs_error_le_nu_sq`,
  `fl_higherPrecisionRecursiveSum_abs_error_le_gamma`,
  `fl_higherPrecisionRecursiveSum_relError_le_of_high_bound_oneSigned`,
  `fl_higherPrecisionRecursiveSum_relError_le_gamma_oneSigned`
- `IncreasingAbsList`, `IncreasingAbsList.tail`, `insertIncreasingAbs`,
  `insertIncreasingAbs_nil`, `insertIncreasingAbs_cons_of_le`,
  `insertIncreasingAbs_cons_of_not_le`, `insertIncreasingAbs_length`,
  `insertIncreasingAbs_ne_nil`, `insertIncreasingAbs_preserves`,
  `insertionStep`, `insertionStep_cons_cons`,
  `insertionStep_length_cons_cons`, `insertionStep_ne_nil_of_ne_nil`,
  `insertionStep_preserves_increasingAbs_cons_cons`,
  `insertionActiveAfter`,
  `insertionActiveAfter_preserves_increasingAbs`,
  `insertionActiveAfter_ne_nil_of_ne_nil`,
  `insertionActiveAfter_length_le_one_of_length_le_succ`,
  `insertionActiveAfter_full_length_le_one`,
  `insertionActiveAfter_full_length_eq_one_of_ne_nil`,
  `insertionActiveAfter_full_eq_singleton_of_ne_nil`,
  `fl_insertionSumList`,
  `fl_insertionSumList_eq_of_activeAfter_eq_singleton`,
  `fl_insertionSumList_eq_terminal_singleton_of_ne_nil`,
  `fl_insertionSumList_nil`, `fl_insertionSumList_singleton`,
  `fl_insertionSumList_pair`
- `InsertionScheduleTree`, `InsertionScheduleTree.eval`,
  `InsertionScheduleTree.leaves`, `InsertionScheduleTree.leafCount`,
  `InsertionScheduleTree.maxLeafDepth`, `InsertionScheduleTree.exactEval`,
  `InsertionScheduleTree.exactMergeCost`,
  `InsertionScheduleTree.weightedLeafDepthCost`,
  `InsertionScheduleTree.leafDepthWeights`,
  `InsertionScheduleTree.weightedDepthPairsCost`,
  `InsertionScheduleTree.leafCount_pos`,
  `InsertionScheduleTree.one_lt_leafCount_node`,
  `InsertionScheduleTree.exactMergeCost_nonneg`,
  `InsertionScheduleTree.weightedDepthPairsCost_eq_of_perm`,
  `InsertionScheduleTree.exists_two_smallest_weight_decomposition`,
  `InsertionScheduleTree.exists_two_smallest_weight_decomposition_components`,
  `InsertionScheduleTree.exactEval_eq_leaves_sum`,
  `InsertionScheduleTree.exactEval_eq_of_leaves_perm`,
  `InsertionScheduleTree.leafDepthWeights_weights_eq_leaves`,
  `InsertionScheduleTree.leaves_eq_of_leafDepthWeights_pair_display`,
  `InsertionScheduleTree.leaves_eq_of_leafDepthWeights_single_display`,
  `InsertionScheduleTree.leafDepthWeights_length`,
  `InsertionScheduleTree.depth_le_maxLeafDepth`,
  `InsertionScheduleTree.succ_depth_le_maxLeafDepth_of_one_lt_leafCount`,
  `InsertionScheduleTree.leafDepthWeights_depth_le_maxLeafDepth`,
  `InsertionScheduleTree.two_smallest_depths_le_deepest_parent_context`,
  `InsertionScheduleTree.exists_deepest_sibling_leaf_pair`,
  `InsertionScheduleTree.weightedLeafDepthCost_eq_weightedDepthPairsCost`,
  `InsertionScheduleTree.weightedLeafDepthCost_eq_of_leafDepthWeights_perm`,
  `InsertionScheduleTree.weightedLeafDepthCost_succ_eq_add_exactEval`,
  `InsertionScheduleTree.weightedLeafDepthCost_node_eq_children_at_depth_add_exactEval`,
  `InsertionScheduleTree.weightedLeafDepthCost_node_leaf_leaf_eq_contract`,
  `InsertionScheduleTree.weightedDepthPairsCost_pair_contract_eq`,
  `InsertionScheduleTree.SiblingLeafContract`,
  `InsertionScheduleTree.SiblingLeafContract.exactEval_eq`,
  `InsertionScheduleTree.SiblingLeafContract.leafCount_eq_succ`,
  `InsertionScheduleTree.SiblingLeafContract.contracted_leafCount_lt`,
  `InsertionScheduleTree.SiblingLeafContract.exists_leaves_context`,
  `InsertionScheduleTree.SiblingLeafContract.exists_leafDepthWeights_context`,
  `InsertionScheduleTree.SiblingLeafContract.exists_leafDepthWeights_and_leaves_context`,
  `InsertionScheduleTree.SiblingLeafContract.exists_leafDepthWeights_context_with_relabel_contract`,
  `InsertionScheduleTree.SiblingLeafContract.relabelLeaves_contract_of_context_lengths`,
  `InsertionScheduleTree.SiblingLeafContract.leaves_perm_of_contracted_perm`,
  `InsertionScheduleTree.SiblingLeafContract.contracted_perm_of_leaves_perm`,
  `InsertionScheduleTree.SiblingLeafContract.exists_expansion_of_mem`,
  `InsertionScheduleTree.SiblingLeafContract.contracted_leaves_nonnegative`,
  `InsertionScheduleTree.SiblingLeafContract.weightedLeafDepthCost_eq`,
  `InsertionScheduleTree.exists_deepest_sibling_leaf_contract`,
  `InsertionScheduleTree.exists_deepest_sibling_leaf_contract_with_parent_context`,
  `InsertionScheduleTree.exists_deepest_sibling_leaf_contract_with_relabel_parent_context`,
  `InsertionScheduleTree.exists_deepest_sibling_leaf_contract_with_branch_bridge`,
  `InsertionScheduleTree.exists_deepest_sibling_leaf_contract_with_leaf_context`,
  `InsertionScheduleTree.weightedDepthPairsCost_of_perm_le_and_weights_perm`,
  `InsertionScheduleTree.weightedLeafDepthCost_nonneg_of_leaves_nonnegative`,
  `InsertionScheduleTree.weightedLeafDepthCost_mono_startDepth_of_leaves_nonnegative`,
  `InsertionScheduleTree.weightedLeafDepthCost_leaf_pair_exchange_le`,
  `InsertionScheduleTree.weightedDepthPairsCost_pair_exchange_le`,
  `InsertionScheduleTree.weightedDepthPairsCost_pair_exchange_separated_le`,
  `InsertionScheduleTree.weightedDepthPairsCost_pair_exchange_separated_of_perm_le_and_weights_perm`,
  `InsertionScheduleTree.weightedDepthPairsCost_pair_exchange_of_context_min_le_and_weights_perm`,
  `InsertionScheduleTree.weightedDepthPairsCost_two_pair_exchange_separated_le`,
  `InsertionScheduleTree.weightedDepthPairsCost_two_pair_exchange_separated_of_perm_le`,
  `InsertionScheduleTree.weightedDepthPairsCost_two_pair_exchange_of_context_min_le`,
  `InsertionScheduleTree.exists_selected_relative_to_adjacent_pair`,
  `InsertionScheduleTree.exists_two_selected_slots_of_perm_cons_cons`,
  `InsertionScheduleTree.exists_second_position_of_first_before_adjacent_pair`,
  `InsertionScheduleTree.exists_second_position_of_first_after_adjacent_pair`,
  `InsertionScheduleTree.exists_pair_decomposition_of_weights_perm_cons_cons`,
  `InsertionScheduleTree.weightedDepthPairsCost_two_pair_exchange_of_context_min_le_and_weights_perm`,
  `InsertionScheduleTree.weightedDepthPairsCost_two_pair_exchange_of_two_smallest_decomposition_le_and_weights_perm`,
  `InsertionScheduleTree.weightedDepthPairsCost_pair_exchange_of_left_deepest_two_smallest_decomposition_le_and_weights_perm`,
  `InsertionScheduleTree.weightedDepthPairsCost_pair_exchange_of_right_deepest_two_smallest_decomposition_le_and_weights_perm`,
  `InsertionScheduleTree.weightedDepthPairsCost_pair_exchange_of_left_deepest_second_two_smallest_decomposition_le_and_weights_perm`,
  `InsertionScheduleTree.weightedDepthPairsCost_pair_exchange_of_right_deepest_second_two_smallest_decomposition_le_and_weights_perm`,
  `InsertionScheduleTree.TwoSmallestDeepestExchangeBranch`,
  `InsertionScheduleTree.weightedDepthPairsCost_two_smallest_deepest_exchange_branch_le_and_weights_perm`,
  `InsertionScheduleTree.weightedLeafDepthCost_two_smallest_deepest_exchange_branch_realized_le_and_leaves_perm`,
  `InsertionScheduleTree.relabelLeaves_leaves_eq`,
  `InsertionScheduleTree.relabelLeaves_leafDepthWeights_eq_zip`,
  `InsertionScheduleTree.relabelLeaves_leafDepthWeights_eq_pairs_of_depths_eq`,
  `InsertionScheduleTree.relabelLeaves_leaves_eq_pairs_of_depths_eq`,
  `InsertionScheduleTree.exists_relabelLeaves_leafDepthWeights_eq_of_depths_eq`,
  `InsertionScheduleTree.exists_relabelLeaves_for_two_smallest_deepest_exchange_branch_of_depths_eq`,
  `InsertionScheduleTree.exists_relabelLeaves_contract_for_two_smallest_deepest_exchange_branch_of_context_lengths`,
  `InsertionScheduleTree.exists_relabelLeaves_contract_for_two_smallest_deepest_exchange_branch_of_explicit_context_lengths`,
  `InsertionScheduleTree.exists_relabelLeaves_contract_for_two_pair_exchange_after_contracted_pair`,
  `InsertionScheduleTree.exists_relabelLeaves_contract_for_two_pair_exchange_reverse_after_contracted_pair`,
  `InsertionScheduleTree.exists_relabelLeaves_contract_for_two_pair_exchange_before_contracted_pair`,
  `InsertionScheduleTree.exists_relabelLeaves_contract_for_two_pair_exchange_reverse_before_contracted_pair`,
  `InsertionScheduleTree.exists_relabelLeaves_contract_for_two_pair_exchange_around_contracted_pair`,
  `InsertionScheduleTree.exists_relabelLeaves_contract_for_two_pair_exchange_reverse_around_contracted_pair`,
  `InsertionScheduleTree.exists_relabelLeaves_contract_for_left_deepest_first_smallest_after_contracted_pair`,
  `InsertionScheduleTree.exists_relabelLeaves_contract_for_right_deepest_first_smallest_after_contracted_pair`,
  `InsertionScheduleTree.exists_relabelLeaves_contract_for_left_deepest_second_smallest_after_contracted_pair`,
  `InsertionScheduleTree.exists_relabelLeaves_contract_for_right_deepest_second_smallest_after_contracted_pair`,
  `InsertionScheduleTree.exists_relabelLeaves_contract_for_left_deepest_first_smallest_before_contracted_pair`,
  `InsertionScheduleTree.exists_relabelLeaves_contract_for_right_deepest_first_smallest_before_contracted_pair`,
  `InsertionScheduleTree.exists_relabelLeaves_contract_for_left_deepest_second_smallest_before_contracted_pair`,
  `InsertionScheduleTree.exists_relabelLeaves_contract_for_right_deepest_second_smallest_before_contracted_pair`,
  `InsertionScheduleTree.exists_relabelLeaves_contract_for_deepest_pair_noop`,
  `InsertionScheduleTree.exists_relabelLeaves_contract_for_first_before_contracted_pair_nonoverlap_anywhere`,
  `InsertionScheduleTree.exists_relabelLeaves_contract_for_first_after_contracted_pair_nonoverlap_anywhere`,
  `InsertionScheduleTree.exists_relabelLeaves_contract_for_first_before_contracted_pair_anywhere`,
  `InsertionScheduleTree.exists_relabelLeaves_contract_for_first_after_contracted_pair_anywhere`,
  `InsertionScheduleTree.exists_relabelLeaves_contract_for_left_deepest_first_two_smallest_anywhere`,
  `InsertionScheduleTree.exists_relabelLeaves_contract_for_right_deepest_first_two_smallest_anywhere`,
  `InsertionScheduleTree.exists_relabelLeaves_contract_for_two_smallest_deepest_pair_anywhere_of_occurrence_classifiers`,
  `InsertionScheduleTree.exists_relabelLeaves_contract_for_left_deepest_first_two_smallest_anywhere_of_context`,
  `InsertionScheduleTree.exists_relabelLeaves_contract_for_right_deepest_first_two_smallest_anywhere_of_context`,
  `InsertionScheduleTree.exists_relabelLeaves_contract_for_first_before_contracted_pair_anywhere_of_context`,
  `InsertionScheduleTree.exists_relabelLeaves_contract_for_first_after_contracted_pair_anywhere_of_context`,
  `InsertionScheduleTree.exists_relabelLeaves_contract_for_two_smallest_deepest_pair_anywhere`,
  `InsertionScheduleTree.exists_relabelLeaves_contract_for_two_smallest_deepest_pair_anywhere_of_context`,
  `InsertionScheduleTree.exists_relabelLeaves_contract_for_two_smallest_deepest_pair_anywhere_with_contracted_perm`,
  `InsertionScheduleTree.exists_relabelLeaves_contract_for_two_smallest_deepest_pair_anywhere_with_induction_data`,
  `InsertionScheduleTree.exists_relabelLeaves_contract_for_two_smallest_deepest_pair_anywhere_of_context_with_contracted_perm`,
  `InsertionScheduleTree.exists_relabelLeaves_contract_for_two_smallest_deepest_pair_anywhere_of_context_with_induction_data`,
  `InsertionScheduleTree.exists_relabelLeaves_contract_for_two_smallest_deepest_pair_anywhere_with_induction_data_of_tree`,
  `InsertionScheduleTree.exists_tree_for_deepest_pair_noop_eq`,
  `InsertionScheduleTree.exists_tree_for_two_pair_exchange_of_two_smallest_decomposition_eq`,
  `InsertionScheduleTree.exists_tree_for_two_pair_exchange_reverse_of_two_smallest_decomposition_eq`,
  `InsertionScheduleTree.exists_tree_for_two_pair_exchange_before_deepest_of_two_smallest_decomposition_eq`,
  `InsertionScheduleTree.exists_tree_for_two_pair_exchange_reverse_before_deepest_of_two_smallest_decomposition_eq`,
  `InsertionScheduleTree.exists_tree_for_two_pair_exchange_around_deepest_of_two_smallest_decomposition_eq`,
  `InsertionScheduleTree.exists_tree_for_two_pair_exchange_reverse_around_deepest_of_two_smallest_decomposition_eq`,
  `InsertionScheduleTree.exists_tree_for_left_deepest_two_smallest_decomposition_eq`,
  `InsertionScheduleTree.exists_tree_for_right_deepest_two_smallest_decomposition_eq`,
  `InsertionScheduleTree.exists_tree_for_left_deepest_second_two_smallest_decomposition_eq`,
  `InsertionScheduleTree.exists_tree_for_right_deepest_second_two_smallest_decomposition_eq`,
  `InsertionScheduleTree.exists_tree_for_left_deepest_two_smallest_before_deepest_decomposition_eq`,
  `InsertionScheduleTree.exists_tree_for_right_deepest_two_smallest_before_deepest_decomposition_eq`,
  `InsertionScheduleTree.exists_tree_for_left_deepest_second_two_smallest_before_deepest_decomposition_eq`,
  `InsertionScheduleTree.exists_tree_for_right_deepest_second_two_smallest_before_deepest_decomposition_eq`,
  `InsertionScheduleTree.exists_tree_for_first_before_deepest_two_smallest_nonoverlap_anywhere`,
  `InsertionScheduleTree.exists_tree_for_first_after_deepest_two_smallest_nonoverlap_anywhere`,
  `InsertionScheduleTree.exists_tree_for_first_before_deepest_two_smallest_anywhere`,
  `InsertionScheduleTree.exists_tree_for_first_after_deepest_two_smallest_anywhere`,
  `InsertionScheduleTree.exists_tree_for_left_deepest_first_two_smallest_anywhere`,
  `InsertionScheduleTree.exists_tree_for_right_deepest_first_two_smallest_anywhere`,
  `InsertionScheduleTree.exists_tree_for_two_smallest_deepest_pair_anywhere`,
  `InsertionScheduleTree.exists_tree_for_two_smallest_deepest_pair_anywhere_pair_witness`,
  `InsertionScheduleTree.exists_tree_with_two_smallest_at_deepest_pair`,
  `InsertionScheduleTree.GreedyInsertionTree`,
  `InsertionScheduleTree.exists_greedyInsertionTree_weightedLeafDepthCost_le`,
  `InsertionScheduleTree.exists_greedyInsertionTree_exactMergeCost_le`,
  `InsertionScheduleTree.GreedyInsertionTree.weightedLeafDepthCost_le`,
  `InsertionScheduleTree.GreedyInsertionTree.exactMergeCost_le`,
  `InsertionScheduleTree.exactEval_nonneg_of_leaves_nonnegative`,
  `InsertionScheduleTree.exactMergeCost_node_of_nonnegative`,
  `InsertionScheduleTree.exactMergeCost_eq_weightedLeafDepthCost_of_leaves_nonnegative`,
  `InsertionScheduleTree.eval_exactWithUnitRoundoff`,
  `InsertionScheduleTree.toSumTree_eval_exactWithUnitRoundoff`,
  `InsertionScheduleTree.toSumTree_runningErrorBudget_exactWithUnitRoundoff`,
  `SumTree.runningErrorBudget_exactWithUnitRoundoff_greedyInsertion_le`,
  `SumTree.toInsertionScheduleTree`,
  `SumTree.toInsertionScheduleTree_eval`,
  `SumTree.toInsertionScheduleTree_exactEval`,
  `SumTree.toInsertionScheduleTree_leafCount`,
  `SumTree.toInsertionScheduleTree_leaves_nonnegative`,
  `SumTree.eval_exactWithUnitRoundoff`,
  `SumTree.runningErrorBudget_exactWithUnitRoundoff_eq_toInsertionScheduleTree_exactMergeCost`,
  `SumTree.runningErrorBudget_exactWithUnitRoundoff_eq_weightedLeafDepthCost_of_nonnegative`,
  `InsertionScheduleItem`,
  `InsertionScheduleItem.source`, `insertionScheduleValues`,
  `insertionScheduleLeaves`, `InsertionScheduleItemContract`,
  `InsertionScheduleItemsContract`,
  `InsertionScheduleItemsContract.values_eq`,
  `InsertionScheduleItemsContract.singleton_left`,
  `insertIncreasingAbs_perm`, `insertIncreasingAbs_nonnegative`,
  `insertInsertionScheduleItemIncreasingAbs`,
  `insertInsertionScheduleItemIncreasingAbs_values`,
  `insertInsertionScheduleItemIncreasingAbs_perm`,
  `insertInsertionScheduleItemIncreasingAbs_contract_item`,
  `insertInsertionScheduleItemIncreasingAbs_contract_list`,
  `insertInsertionScheduleItemIncreasingAbs_leaves_perm`,
  `initialInsertionScheduleItems`,
  `initialInsertionScheduleItems_values`,
  `initialInsertionScheduleItems_leaves`,
  `initialInsertionScheduleItems_insertIncreasingAbs`,
  `insertionScheduleStep`,
  `insertionScheduleStep_values`, `insertionScheduleStep_leaves_perm`,
  `insertionScheduleStep_contract`,
  `insertionScheduleAfter`, `insertionScheduleAfter_values`,
  `insertionScheduleAfter_contract`,
  `insertionScheduleAfter_contract_singleton_left`,
  `insertionScheduleAfter_leaves_perm`,
  `insertionScheduleAfter_full_eq_singleton_of_ne_nil`,
  `insertionScheduleAfter_full_greedy_exactWithUnitRoundoff_of_ne_nil`,
  `fl_insertionSumList_has_list_schedule_of_ne_nil`,
  `fl_insertionSumList_has_greedy_schedule_exactWithUnitRoundoff_of_ne_nil`,
  `fl_insertionSumList_exactWithUnitRoundoff_greedy_runningErrorBudget_le`,
  `fl_insertionSumList_has_sumTree_shape_of_ne_nil`, `fl_insertionSumList_has_sumTree_eval_of_ne_nil`
- `insertionPowersFourTree`, `insertionPowersFourTree_numAdds`,
  `insertionPowersFourTree_depth`, `insertionPowersFour_exact_order`,
  `fl_insertionPowersFour`, `fl_insertionPowersFour_eq`,
  `fl_insertionPowersFour_eq_recursiveSum`,
  `insertionPowersFour_backward_error`,
  `insertionPowersFour_forward_error_bound`,
  `insertionPowersFour_running_error_bound_from_inverse_models`,
  `insertionPowersFour_oneSigned`,
  `insertionPowersFour_forward_error_bound_oneSigned`,
  `insertionPowersFour_relError_le_gamma_of_oneSigned`
- `insertionNearOneFourTree`, `insertionNearOneFourTree_numAdds`,
  `insertionNearOneFourTree_depth`, `insertionNearOneFour_exact_order`,
  `fl_insertionNearOneFour`, `fl_insertionNearOneFour_eq`,
  `fl_insertionNearOneFour_eq_pairwiseSum`,
  `insertionNearOneFour_backward_error`,
  `insertionNearOneFour_forward_error_bound`,
  `insertionNearOneFour_running_error_bound_from_inverse_models`,
  `insertionNearOneFour_oneSigned`,
  `insertionNearOneFour_forward_error_bound_oneSigned`,
  `insertionNearOneFour_relError_le_gamma_of_oneSigned`
- `IncreasingMagnitudeOrder`, `StrictIncreasingMagnitudeOrder`,
  `DecreasingMagnitudeOrder`, `StrictDecreasingMagnitudeOrder`,
  `IncreasingMagnitudeOrder.of_strict`,
  `DecreasingMagnitudeOrder.of_strict`, `fl_recursiveSumInOrder`,
  `sum_orderedInput_eq_sum`, `fl_recursiveSumInOrder_refl`,
  `DecreasingAbsList`, `DecreasingAbsList.tail`,
  `insertDecreasingAbs`, `insertDecreasingAbs_perm`,
  `insertDecreasingAbs_preserves`, `list_sum_eq_of_perm`,
  `increasingAbsSort`, `increasingAbsSort_sorted`,
  `increasingAbsSort_perm`, `increasingAbsSort_sum_eq`,
  `decreasingAbsSort`, `decreasingAbsSort_sorted`,
  `decreasingAbsSort_perm`, `decreasingAbsSort_sum_eq`,
  `recursiveExactPrefixBudgetFrom`, `recursiveExactPrefixBudget`,
  `recursiveRoundedPrefixBudgetFrom`, `recursiveRoundedPrefixBudget`,
  `recursiveRoundedPrefixBudgetFrom_exactWithUnitRoundoff`,
  `recursiveRoundedPrefixBudget_exactWithUnitRoundoff`,
  `recursiveExactPrefixBudgetFrom_insertIncreasingAbs_le_cons_of_nonnegative_sorted`,
  `increasingAbsSort_recursiveExactPrefixBudgetFrom_le`,
  `increasingAbsSort_recursiveExactPrefixBudget_le`,
  `increasingAbsSort_recursiveRoundedPrefixBudget_exactWithUnitRoundoff_le`,
  `IncreasingAbsList.cons_of_abs_le_all`,
  `IncreasingAbsList.sortedLE_of_nonnegative`,
  `psumSelect`, `psumSelect_eq_none_iff`, `psumSelect_perm`,
  `psumSelect_min`, `psumSelect_mem`, `psumSelectComparisonCost`,
  `psumSelectComparisonCost_eq_pred_length`,
  `psumSelect_le_of_nonnegative`, `psumSelect_rest_nonnegative`,
  `psumTriangularComparisonCost`, `psumOrderFromFuel`,
  `psumOrderFrom`, `psumOrder`, `psumOrderFromFuelComparisonCost`,
  `psumOrderFromComparisonCost`, `psumOrderComparisonCost`,
  `PsumGreedyOrderFrom`,
  `PsumGreedyOrderFrom.head_min`, `PsumGreedyOrderFrom.perm`,
  `psumOrderFromFuel_perm`, `psumOrderFrom_perm`,
  `psumOrder_perm`, `psumOrderFromFuel_greedyTrace`,
  `psumOrderFrom_greedyTrace`, `psumOrder_greedyTrace`,
  `psumOrderFromFuel_increasingAbs_of_nonnegative`,
  `psumOrderFrom_increasingAbs_of_nonnegative`,
  `psumOrder_increasingAbs_of_nonnegative`,
  `psumOrder_eq_increasingAbsSort_of_nonnegative`,
  `psumOrder_recursiveExactPrefixBudget_le`,
  `psumOrder_recursiveRoundedPrefixBudget_exactWithUnitRoundoff_le`,
  `psumOrderFromFuelComparisonCost_eq_triangular`,
  `psumOrderFromComparisonCost_eq_triangular`,
  `psumOrderComparisonCost_eq_triangular`,
  `psumLogSearchStepBudget`, `psumLogSearchComparisonBudget`,
  `PsumLogSearchTraceFrom`,
  `PsumLogSearchTraceFrom.greedyTrace`,
  `PsumLogSearchTraceFrom.perm`,
  `PsumLogSearchTraceFrom.cost_le_budget`,
  `psumLogSearchStepBudget_mono`,
  `psumLogSearchComparisonBudget_le_mul_stepBudget`,
  `PsumLowerNeighbor`, `PsumLowerNeighbor.abs_add_le_of_le_neg_acc`,
  `PsumLowerNeighbor.abs_add_le_all_of_all_le_neg_acc`,
  `PsumUpperNeighbor`, `PsumUpperNeighbor.abs_add_le_of_neg_acc_le`,
  `PsumUpperNeighbor.abs_add_le_all_of_neg_acc_le_all`,
  `psumNeighborChoice_mem_and_min`, `sortedLE_erase`,
  `cons_erase_perm_of_mem`, `psumSortedLowerSearch`,
  `psumSortedUpperSearch`, `psumClosestNeighbor`,
  `psumSortedLowerSearch_eq_none_iff`,
  `psumSortedUpperSearch_eq_none_iff`,
  `psumSortedLowerSearch_neighbor`, `psumSortedUpperSearch_neighbor`,
  `psumSortedNeighborSelect`, `psumSortedNeighborSelect_eq_none_iff`,
  `psumSortedNeighborSelect_mem_and_min`,
  `psumSortedNeighborSelect_erase_sorted_perm_length_min`,
  `PsumMinOrderFrom`, `PsumMinOrderFrom.perm`,
  `psumSortedNeighborOrderFromFuel`,
  `psumSortedNeighborOrderFromFuel_minTrace`,
  `PsumSortedNeighborLogSearchTraceFrom`,
  `PsumSortedNeighborLogSearchTraceFrom.minTrace`,
  `PsumSortedNeighborLogSearchTraceFrom.perm`,
  `PsumSortedNeighborLogSearchTraceFrom.cost_le_budget`,
  `psumSortedNeighborOrderFromFuel_logSearchTrace`,
  `psumOrderFromFuel_logSearchTrace`,
  `psumOrderFrom_logSearchTrace`, `psumOrder_logSearchTrace`,
  `psumOrder_logSearchComparisonCost_le_mul_stepBudget`,
  `increasingAbsSortVector`, `increasingAbsSortVector_toList`,
  `increasingAbsSortVector_sorted`, `increasingAbsSortVector_perm`,
  `increasingAbsSortVector_sum_eq`,
  `increasingAbsSortVector_recursiveRoundedPrefixBudget_exactWithUnitRoundoff_le`,
  `decreasingAbsSortVector`,
  `decreasingAbsSortVector_toList`, `decreasingAbsSortVector_sorted`,
  `decreasingAbsSortVector_perm`, `decreasingAbsSortVector_sum_eq`,
  `psumOrderVector`, `psumOrderVector_toList`, `psumOrderVector_perm`,
  `psumOrderVector_greedyTrace`,
  `psumOrderVector_sorted_of_nonnegative`,
  `psumOrderVector_eq_increasingAbsSortVector_of_nonnegative`,
  `psumOrderVector_recursiveRoundedPrefixBudget_exactWithUnitRoundoff_le`,
  `psumOrderVector_sum_eq`
- `p91RecursiveFourTree`, `p91IncreasingInput`, `p91PsumInput`,
  `p91DecreasingInput`, `P91CancellationRounding`,
  `fl_p91Increasing`, `fl_p91Psum`, `fl_p91Decreasing`,
  `p91Increasing_exact_sum`, `p91Psum_exact_sum`,
  `p91Decreasing_exact_sum`, `p91Increasing_sum_abs_eq`,
  `p91Psum_sum_abs_eq`, `p91Decreasing_sum_abs_eq`,
  `p91Increasing_heavyCancellationAtLeast`,
  `p91Psum_heavyCancellationAtLeast`,
  `p91Decreasing_heavyCancellationAtLeast`,
  `fl_p91Increasing_eq_zero`,
  `fl_p91Psum_eq_zero`, `fl_p91Decreasing_eq_one`,
  `p91Increasing_relError_eq_one`, `p91Psum_relError_eq_one`,
  `fl_p91Decreasing_eq_exact_sum`,
  `relError_exact_eq_zero`, `relError_zero_eq_one_of_ne_zero`,
  `relError_pos_of_ne_exact`,
  `relError_le_of_abs_sub_le_mul_abs`,
  `heavyCancellation_postCancellation_bound_beats_competitor`,
  `heavyCancellation_exact_result_beats_inexact_result`,
  `heavyCancellation_exact_result_beats_zero_result`,
  `p91_decreasing_beats_increasing_under_heavyCancellation`,
  `p91_decreasing_beats_psum_under_heavyCancellation`,
  `p91_decreasing_postCancellation_bound_beats_increasing`,
  `p91_decreasing_postCancellation_bound_beats_psum`,
  `p91RecursiveFourTree_eval_increasing_eq`,
  `p91RecursiveFourTree_eval_psum_eq`,
  `p91RecursiveFourTree_eval_decreasing_eq`,
  `p91Increasing_runningErrorBudget_eq`,
  `p91Psum_runningErrorBudget_eq`,
  `p91Decreasing_runningErrorBudget_eq`,
  `p91_runningErrorBudget_ranking`
- `CorrectionFormulaTrace`, `CorrectionFormulaTrace.exact`,
  `correctionFormulaTrace`, `correctionFormulaTrace_s`,
  `correctionFormulaTrace_e`,
  `finiteCorrectionFormulaTrace`,
  `finiteCorrectionFormulaTrace_s`,
  `finiteCorrectionFormulaTrace_e`,
  `finiteCorrectionFormulaTrace_exact_of_exact_sub_and_finite_error_add`,
  `finiteCorrectionFormulaTrace_exact_of_sterbenz_and_finite_error_add`,
  `finiteCorrectionFormulaTrace_exact_of_signed_sterbenz_and_finite_error_add`,
  `finiteCorrectionFormulaTrace_exact_of_two_signed_sterbenz`,
  `FastTwoSumFiniteCertificate`,
  `FastTwoSumFiniteCertificate.finite_s_unconditional`,
  `FastTwoSumFiniteCertificate.of_error_obligations`,
  `FastTwoSumFiniteCertificate.of_two_signed_sterbenz`,
  `correctionFormula_abs_order_not_imply_signed_sterbenz_exact_sum`,
  `FastTwoSumFiniteCertificate.of_exact_add`,
  `finiteCorrectionFormulaTrace_exact_of_fastTwoSumFiniteCertificate`,
  `finiteCorrectionFormulaTrace_exact_of_exact_add`,
  `correctionFormulaAbstractCounterexampleFPModel`,
  `correctionFormulaAbstractCounterexample_abs_order`,
  `correctionFormulaAbstractCounterexample_not_exact`
- `NoGuardCorrectionFormulaTrace`,
  `NoGuardCorrectionFormulaTrace.exact`,
  `NoGuardCorrectionFormulaTrace.model`,
  `NoGuardCorrectionFormulaTrace.toCorrectionFormulaTrace`,
  `noGuardCorrectionFormulaTrace`, `noGuardCorrectionFormulaTrace_s`,
  `noGuardCorrectionFormulaTrace_aMinusS`,
  `noGuardCorrectionFormulaTrace_e`,
  `noGuardCorrectionFormulaTrace_model`,
  `noGuardCorrectionFormulaCounterexample`,
  `noGuardCorrectionFormulaCounterexample_abs_order`,
  `noGuardCorrectionFormulaCounterexample_model`,
  `noGuardCorrectionFormulaCounterexample_not_exact`,
  `noGuardCorrectionFormulaCounterexample_toCorrectionFormulaTrace_not_exact`
- `KahanState`, `KahanState.zero`, `KahanStepTrace`,
  `KahanStepTrace.nextState`, `kahanStepTrace`, `kahanStep`,
  `kahanStepTrace_temp`, `kahanStepTrace_y`, `kahanStepTrace_s`,
  `kahanStepTrace_e`, `kahanStepTrace_correctionFormulaTrace`,
  `kahanStepTrace_compensated_total_eq_of_exact_y_and_correction`,
  `kahanStep_compensated_total_eq_of_exact_y_and_correction`,
  `kahanPrefixState_compensated_total_eq_sum_of_exact_steps`,
  `fl_kahanState_compensated_total_eq_sum_of_exact_steps`,
  `fl_kahanSum_add_correction_eq_sum_of_exact_steps`,
  `kahanPrefixState`, `kahanTrace`,
  `fl_kahanState`, `fl_kahanSum`, `fl_kahanCorrection`,
  `fl_kahanState_eq_prefixState`, `fl_kahanSum_eq_state_s`,
  `fl_kahanCorrection_eq_state_e`, `fl_kahanFinalCorrectedSum`,
  `fl_kahanFinalCorrectedSum_eq_add_correction`,
  `fl_kahanFinalCorrectedSum_eq_sum_of_exact_steps_and_final_add`,
  `fl_kahanState_exactWithUnitRoundoff`,
  `fl_kahanSum_exactWithUnitRoundoff`,
  `fl_kahanCorrection_exactWithUnitRoundoff`,
  `fl_kahanFinalCorrectedSum_exactWithUnitRoundoff`,
  `kahan_backward_error_forward_bound_core`,
  `fl_kahanSum_forward_error_bound_of_backward`,
  `fl_kahanSum_relError_le_of_backward_oneSigned`,
  `fl_kahanFinalCorrectedSum_forward_error_bound_of_backward`,
  `fl_kahanFinalCorrectedSum_relError_le_of_backward_oneSigned`
- `kahanNoGuardStepTrace`, `kahanNoGuardStep`,
  `kahanNoGuardStepTrace_temp`, `kahanNoGuardStepTrace_y`,
  `kahanNoGuardStepTrace_s`, `kahanNoGuardStepTrace_e`,
  `kahanNoGuardPrefixState`, `kahanNoGuardTrace`,
  `fl_kahanNoGuardState`, `fl_kahanNoGuardSum`,
  `fl_kahanNoGuardCorrection`,
  `fl_kahanNoGuardState_eq_prefixState`,
  `fl_kahanNoGuardSum_eq_state_s`,
  `fl_kahanNoGuardCorrection_eq_state_e`,
  `kahanNoGuardCounterexampleModel`,
  `kahanNoGuardCounterexampleInput`,
  `fl_kahanNoGuardCounterexampleState_eq`,
  `fl_kahanNoGuardCounterexampleSum_eq`,
  `fl_kahanNoGuardCounterexampleCorrection_eq`,
  `kahanNoGuardCounterexample_exactSum_eq`,
  `kahanNoGuardCounterexample_relError_eq_one`
- `AlternativeCompensatedStepTrace`,
  `AlternativeCompensatedStepTrace.nextSum`,
  `alternativeCompensatedStepTrace`,
  `alternativeCompensatedStepTrace_temp`,
  `alternativeCompensatedStepTrace_s`,
  `alternativeCompensatedStepTrace_e`,
  `alternativeCompensatedPrefixSum`, `alternativeCompensatedTrace`,
  `alternativeCompensatedCorrections`,
  `fl_alternativeCompensatedMainSum`,
  `fl_alternativeCompensatedGlobalCorrection`,
  `fl_alternativeCompensatedSum`,
  `fl_alternativeCompensatedMainSum_eq_prefixSum`,
  `fl_alternativeCompensatedGlobalCorrection_eq_recursiveSum`,
  `fl_alternativeCompensatedSum_eq_add_globalCorrection`,
  `alternativeCompensatedStepTrace_correctionFormulaTrace`,
  `alternativeCompensatedStepTrace_main_plus_correction_eq_of_correction`,
  `alternativeCompensatedPrefixCorrection`,
  `alternativeCompensatedPrefixSum_add_corrections_eq_sum_of_exact_steps`,
  `fl_alternativeCompensatedMainSum_add_exact_corrections_eq_sum_of_exact_steps`,
  `fl_alternativeCompensatedSum_eq_sum_of_exact_steps_and_exact_correction_sum`,
  `fl_alternativeCompensatedMainSum_exactWithUnitRoundoff`,
  `alternativeCompensatedCorrections_exactWithUnitRoundoff`,
  `fl_alternativeCompensatedGlobalCorrection_exactWithUnitRoundoff`,
  `fl_alternativeCompensatedSum_exactWithUnitRoundoff`,
  `fl_alternativeCompensatedSum_forward_error_bound_of_backward`,
  `fl_alternativeCompensatedSum_relError_le_of_backward_oneSigned`
- `kahanSameSign`, `KahanModifiedNoGuardStepTrace`,
  `KahanModifiedNoGuardStepTrace.nextState`,
  `kahanModifiedNoGuardStepTrace`, `kahanModifiedNoGuardStep`,
  `kahanModifiedNoGuardStepTrace_temp`,
  `kahanModifiedNoGuardStepTrace_y`, `kahanModifiedNoGuardStepTrace_s`,
  `kahanModifiedNoGuardStepTrace_f0`, `kahanModifiedNoGuardStepTrace_f`,
  `kahanModifiedNoGuardStepTrace_e`,
  `kahanModifiedNoGuardPrefixState`, `kahanModifiedNoGuardTrace`,
  `fl_kahanModifiedNoGuardState`, `fl_kahanModifiedNoGuardSum`,
  `fl_kahanModifiedNoGuardCorrection`,
  `fl_kahanModifiedNoGuardState_eq_prefixState`,
  `fl_kahanModifiedNoGuardSum_eq_state_s`,
  `fl_kahanModifiedNoGuardCorrection_eq_state_e`,
  `kahanModifiedNoGuardStep_exactWithUnitRoundoff`,
  `fl_kahanModifiedNoGuardState_exactWithUnitRoundoff`,
  `fl_kahanModifiedNoGuardSum_exactWithUnitRoundoff`,
  `fl_kahanModifiedNoGuardCorrection_exactWithUnitRoundoff`
- `priestSortedByDecreasingAbs`, `priestStrictlySortedByDecreasingAbs`,
  `priestSortedByDecreasingAbs_of_strict`, `PriestState`,
  `priestInitialState`,
  `PriestStepTrace`, `PriestStepTrace.nextState`, `priestStepTrace`,
  `priestStep`, `priestStepTrace_y`, `priestStepTrace_u`,
  `priestStepTrace_t`, `priestStepTrace_upsilon`, `priestStepTrace_z`,
  `priestStepTrace_s`, `priestStepTrace_c`, `priestPrefixState`,
  `priestTrace`, `fl_priestState`, `fl_priestSum`,
  `fl_priestCorrection`, `fl_priestState_eq_prefixState`,
  `fl_priestSum_eq_state_s`, `fl_priestCorrection_eq_state_c`,
  `fl_priestState_exactWithUnitRoundoff`,
  `fl_priestSum_exactWithUnitRoundoff`,
  `fl_priestCorrection_exactWithUnitRoundoff`
- `AccumulatorState`, `AccumulatorOverflowTest`, `accumulatorZero`,
  `accumulatorSet`, `accumulatorSet_self`, `accumulatorSet_of_ne`,
  `accumulatorCascadeFrom`, `accumulatorCascadeFrom_no_overflow`,
  `accumulatorCascadeFrom_overflow_to_next`,
  `accumulatorCascadeFrom_no_next_level`, `accumulatorAddTerm`,
  `accumulatorAddTerm_no_lowest_overflow`, `accumulatorPrefixState`,
  `fl_accumulatorState`, `DecreasingAbsAccumulatorOrder`,
  `fl_accumulatorFinalSum`, `fl_accumulatorSum`,
  `fl_accumulatorState_eq_prefixState`,
  `fl_accumulatorSum_eq_recursive_final_state`,
  `fl_accumulatorSum_uses_decreasing_abs_order`,
  `accumulatorNeverOverflow`, `accumulatorIdentityOrder`,
  `fl_accumulatorState_neverOverflow_zero_exactWithUnitRoundoff`,
  `fl_accumulatorState_neverOverflow_of_ne_zero_exactWithUnitRoundoff`,
  `fl_accumulatorSum_neverOverflow_exactWithUnitRoundoff`,
  `fl_accumulatorSum_singleLevel_neverOverflow_exactWithUnitRoundoff`,
  `DistillationState`, `distillationInitialState`,
  `distillationStateSum`, `distillationInitialState_sum_eq`,
  `DistillationTrace`,
  `DistillationTrace.finalState`, `DistillationTrace.finalComponent`,
  `DistillationTrace.terminatesWithinUnitRoundoff`,
  `distillationTrace_sum_preserved`,
  `distillationTrace_finalState_sum_eq`,
  `distillationTrace_finalState_sum_eq_initial`,
  `distillationTrace_terminatesWithinUnitRoundoff_iff`,
  `distillationTrace_finalComponent_relError_le`,
  `distillationTrace_finalComponent_abs_error_le`
- `fl_pairwiseSum`, `pairwiseSum_backward_error`,
  `pairwiseSum_forward_error_bound`,
  `pairwiseSum_forward_error_bound_oneSigned`,
  `pairwiseSum_relError_le_gamma_of_oneSigned`
- `pairwiseSixTree`, `pairwiseSixTree_depth`,
  `fl_pairwiseSumSixDisplayed`, `fl_pairwiseSumSixDisplayed_eq`,
  `pairwiseSumSixDisplayed_backward_error`,
  `pairwiseSumSixDisplayed_forward_error_bound`
- `pairwiseCarryTree`, `pairwiseCarryTree_depth`,
  `nat_le_two_pow_pred`, `clog2_le_pred`,
  `pairwiseCarryTree_depth_le_linear`,
  `fl_pairwiseCarrySum`, `pairwiseCarrySum_backward_error`,
  `pairwiseCarrySum_forward_error_bound`,
  `pairwiseCarrySum_forward_error_bound_oneSigned`,
  `pairwiseCarrySum_relError_le_gamma_of_oneSigned`
- `scalarFinZeroPad`, `sum_scalarFinZeroPad_eq`,
  `sum_scalarFinZeroPad_abs_eq`,
  `fl_clog2PairwiseSum`, `clog2PairwiseSum_backward_error`,
  `clog2PairwiseSum_forward_error_bound`,
  `clog2PairwiseSum_forward_error_bound_oneSigned`,
  `clog2PairwiseSum_relError_le_gamma_of_oneSigned`
- `OneSigned`, `HeavyCancellationAtLeast`, `sum_abs_eq_sum_of_nonneg`,
  `sum_abs_eq_neg_sum_of_nonpos`, `sum_abs_eq_abs_sum_of_oneSigned`
- `statisticalWeightedRoundingErrorSum`,
  `StatisticalRoundingErrorModel.expectation_weighted_sum_eq_zero`,
  `StatisticalRoundingErrorModel.expectation_weighted_sum_sq_eq_sum_weight_sq_second_moments`,
  `StatisticalRoundingErrorModel.expectation_weighted_sum_sq_le_weight_sq_mul_unit_sq`,
  `StatisticalRoundingErrorModel.rms_weighted_sum_le_sqrt_weight_sq_mul_unit`,
  `SumTree.computedInternalSums`,
  `SumTree.computedInternalSums_length_eq_numAdds`,
  `SumTree.computedInternalSums_abs_sum_eq_runningErrorBudget`,
  `SumTree.statisticalRunningErrorContribution`,
  `SumTree.statisticalRunningErrorContribution_expectation_eq_zero`,
  `SumTree.statisticalRunningErrorContribution_expectation_sq_eq_sum`,
  `SumTree.statisticalRunningErrorContribution_expectation_sq_le`,
  `SumTree.statisticalRunningErrorContribution_rms_le`,
  `Table41Distribution`, `Table41Method`,
  `table41MeanSquareConstant`, `table41NExponent`,
  `table41MeanSquareEstimate`,
  `table41_recursive_constants_rank_uniform`,
  `table41_recursive_constants_rank_exponential`,
  `table41_insertion_constant_lt_pairwise_uniform`,
  `table41_insertion_constant_lt_pairwise_exponential`,
  `table41_recursive_exponents_eq_three`,
  `table41_insertion_pairwise_exponents_eq_two`,
  `table41MeanSquareScale_pos`,
  `table41_recursive_estimates_rank_uniform`,
  `table41_recursive_estimates_rank_exponential`,
  `table41_insertion_estimate_lt_pairwise_uniform`,
  `table41_insertion_estimate_lt_pairwise_exponential`
- `SumTree`, `SumTree.depth`, `SumTree.numAdds`, `SumTree.numAdds_eq`,
  `SumTree.depth_le`, `SumTree.eval`, `SumTree.exactSum`,
  `SumTree.exactSum_eq_sum`
- `SumTree.inverseEvalModel`, `SumTree.runningErrorBudget`,
  `SumTree.runningErrorBudget_nonneg`, `SumTree.runningErrorContribution`,
  `SumTree.exists_runningErrorContribution_of_inverseEvalModel`,
  `SumTree.runningErrorContribution_eq_error`,
  `SumTree.runningErrorContribution_abs_le`,
  `SumTree.running_error_bound_from_inverse_models`,
  `SumTree.running_error_sum_bound_from_inverse_models`
- `SumTree.backward_error`, `SumTree.forward_error`,
  `SumTree.forward_error_oneSigned`,
  `SumTree.relError_le_gamma_of_oneSigned`,
  `SumTree.backward_error_n_minus_one`,
  `SumTree.forward_error_n_minus_one`,
  `SumTree.forward_error_n_minus_one_oneSigned`,
  `SumTree.relError_le_gamma_n_minus_one_of_oneSigned`,
  `gamma_le_two_mul_n_u_of_nu_le_half`,
  `SumTree.relError_le_two_mul_n_minus_one_u_of_oneSigned`
- `SumTree.chainTreeSucc`, `SumTree.chainTreeSucc_depth`,
  `SumTree.chainTreeSucc_eval_eq_recursiveSum`,
  `SumTree.chainTree`, `SumTree.chainTree_depth`,
  `SumTree.chainTree_backward_error`, `SumTree.chainTree_forward_error`
- `SumTree.balancedTree`, `SumTree.balancedTree_depth`,
  `SumTree.balancedTree_backward_error`,
  `SumTree.balancedTree_forward_error`

### C4.3 Psum Sorted-Search Adapter Addendum

The C4.3 ordered-neighbor foundation now has a concrete sorted-list search
adapter.  `psumSortedLowerSearch` and `psumSortedUpperSearch` search a sorted
active list for the predecessor and successor of `-acc`; the theorem pair
`psumSortedLowerSearch_neighbor` and `psumSortedUpperSearch_neighbor` proves
that successful searches return `PsumLowerNeighbor` and `PsumUpperNeighbor`
certificates, while `psumSortedLowerSearch_eq_none_iff` and
`psumSortedUpperSearch_eq_none_iff` discharge the one-sided endpoint cases.
The public selector theorem `psumSortedNeighborSelect_mem_and_min` combines
these searches with `psumNeighborChoice_mem_and_min` to prove that the
sorted-list selector returns a member globally minimizing Higham's Psum
objective `|acc + x|` over the active set, and
`psumSortedNeighborSelect_eq_none_iff` proves that the selector fails exactly on
empty sorted active lists.  The deletion adapter
`psumSortedNeighborSelect_erase_sorted_perm_length_min` further proves that the
erased remainder remains sorted, the selected value consed onto that remainder
permutes back to the prior active list, and the active-list length drops by one.
The extensional trace predicate `PsumMinOrderFrom` records a complete order in
which each emitted head is a global Psum minimizer and the recursive active
list is a one-element deletion permutation of the previous active list;
`psumSortedNeighborOrderFromFuel_minTrace` proves that the fuelled sorted-list
selector realizes such a trace whenever the initial sorted active list has
enough fuel.  The abstract log-cost trace
`PsumSortedNeighborLogSearchTraceFrom` adds the per-step search/delete
comparison cost, `PsumSortedNeighborLogSearchTraceFrom.cost_le_budget` proves
the recursive `psumLogSearchComparisonBudget` bound, and
`psumSortedNeighborOrderFromFuel_logSearchTrace` proves that the fuelled
sorted-neighbor selector realizes this cost trace under the same sortedness and
fuel hypotheses.  A concrete set-valued red-black specialization is now closed
by `psumRealCmp` and the `PsumRBSet` theorem family:
`PsumRBSet.toList_sortedLE` identifies the ordered tree traversal with a sorted
real list, `PsumRBSet.lowerBound_neighbor` and
`PsumRBSet.upperBound_neighbor` prove that concrete red-black lower/upper-bound
queries return the Psum predecessor/successor certificates,
`PsumRBSet.neighborSelect_mem_and_min` proves that the concrete red-black
selector minimizes `|acc + x|`, and
`PsumRBSet.depth_succ_le_stepBudget` plus
`PsumRBSet.eraseValue_depth_succ_le_stepBudget` connect Batteries' red-black
balance/depth invariant to the existing logarithmic Psum step budget.  The
duplicate-aware list bridge is also now closed: `psumCountEntriesExpand`
expands `(value, count)` entries into the source active-list view, while
`psumCountEntriesEraseOne_perm` and `psumCountEntriesEraseOne_length` prove
that decrementing one positive counted occurrence realizes exactly one
list-level deletion by permutation and length drop.  The concrete counted-map
view is now theorem-backed by `PsumCountRBMap`: `PsumCountRBMap.PositiveCounts`
records positive stored multiplicities, `PsumCountRBMap.lowerBound_neighbor`
and `PsumCountRBMap.upperBound_neighbor` prove that key-based red-black
lower/upper-bound queries return Psum predecessor/successor certificates for
the expanded active-list view, `PsumCountRBMap.neighborSelect_mem_and_min`
proves counted-map selector minimality even with duplicate active values, and
`PsumCountRBMap.eraseOne_entries_perm` plus
`PsumCountRBMap.eraseOne_entries_length` lift the duplicate-preserving deletion
bridge to a concrete counted `RBMap`'s `toList` view.  The certified one-step
counted-map package is also closed:
`psumCountEntriesExpand_length_ge_entries_length_of_positive` proves that
positive-count expansion has at least the distinct-entry length,
`PsumCountRBMap.depth_succ_le_stepBudget` bounds the concrete red-black depth
charge by the expanded active-list logarithmic step budget, and
`PsumCountRBMap.stepEntries_certifies` packages a successful selector/decrement
step with selected-member, global-minimizer, duplicate-preserving deletion,
length-drop, and cost certificates, while
`PsumCountRBMap.neighborSelect_eq_none_iff_activeList_eq_nil` and
`PsumCountRBMap.stepEntries_eq_none_iff_activeList_eq_nil` prove that the
selector and executable counted-entry step fail exactly when the expanded
active-list view is empty, and
`PsumCountRBMap.stepEntries_decreases_activeList_length` proves that every
successful counted-entry step strictly decreases the expanded active-list
length.  The positive-count invariant needed by a recursive counted-map loop
is also closed at the counted-entry boundary by
`psumCountEntriesEraseOne_preserves_positive` and
`PsumCountRBMap.stepEntries_preserves_positive_entries`: decrementing one
selected occurrence leaves every remaining multiplicity strictly positive.
The native executable-update substrate is closed for the counted red-black Psum
loop:
`psumRealCmp_eq_eq` identifies concrete comparator equality with ordinary real
equality, `rbNode_append_toList` and `rbNodePath_del_toList` expose the
ordered traversal of Batteries' red-black append/delete-path primitives, and
`PsumCountRBMap.eraseOneNative_toList_of_zoom` proves the concrete
`RBMap.alter` branch traversal for deleting or decrementing a found counted
key.  The global selected-key lift is closed:
`PsumCountRBMap.find?_some_of_mem_toList` and
`PsumCountRBMap.exists_find?_of_mem_activeList` recover a positive native
lookup count from the expanded active-list view, while
`PsumCountRBMap.find?_some_zoom`,
`PsumCountRBMap.eraseOneNative_toList_of_find?`, and
`PsumCountRBMap.eraseOneNative_toList_of_mem_activeList` connect that lookup to
the native zoom branch and concrete traversal.
`PsumCountRBMap.eraseOneNative_activeList_perm` and
`PsumCountRBMap.eraseOneNative_activeList_length` prove that the native next map
realizes the duplicate-aware deletion bridge in the expanded active-list view,
and `PsumCountRBMap.eraseOneNative_preserves_positive` carries the
positive-count invariant on the native map.
The recursive counted-entry composition layer is now closed by
`PsumCountRBMap.EntryStep`,
`PsumCountRBMap.entryStep_of_stepEntries`,
`PsumCountRBMap.EntryLogSearchTraceFrom.minTrace`,
`PsumCountRBMap.EntryLogSearchTraceFrom.perm`, and
`PsumCountRBMap.EntryLogSearchTraceFrom.cost_le_budget`: certified
counted-map steps compose into an expanded-list Psum minimizer trace, preserve
the expanded multiset, and satisfy the recursive logarithmic comparison
budget.  The executable native loop is now closed by `PsumCountRBMap.stepNative`,
`PsumCountRBMap.entryStep_of_stepNative`,
`PsumCountRBMap.stepNative_decreases_activeList_length`,
`PsumCountRBMap.stepNative_preserves_positive`,
`PsumCountRBMap.nativeOrderFromFuel_entryLogSearchTrace`,
`PsumCountRBMap.nativeOrderFrom_entryLogSearchTrace`,
`PsumCountRBMap.nativeOrderFrom_minTrace`,
`PsumCountRBMap.nativeOrderFrom_perm`, and
`PsumCountRBMap.nativeOrderCostFrom_le_budget`.  The focused native-update
dependency checklist is maintained in
`docs/CHAPTER04_C43_PSUM_RBMAP_BOTTLENECK.md` as a closed bottleneck record.

## Not-Proved Chapter 4 Rows

| ID | Source location | Open paper-level item | Missing foundations / next proof target |
|---|---|---|---|
| C4.1 | pp. 88--89 and p. 91 | General insertion summation algorithm and nonnegative optimality for the running-error bound. | The general ordered active-list algorithm, invariant, nonemptiness preservation, terminal-length theorem, singleton terminal-value theorem, final value extraction, and list-shaped binary schedule trace are closed by `fl_insertionSumList`, `insertIncreasingAbs_preserves`, `insertIncreasingAbs_ne_nil`, `insertionActiveAfter_preserves_increasingAbs`, `insertionActiveAfter_ne_nil_of_ne_nil`, `insertionActiveAfter_full_length_le_one`, `insertionActiveAfter_full_length_eq_one_of_ne_nil`, `insertionActiveAfter_full_eq_singleton_of_ne_nil`, `fl_insertionSumList_eq_terminal_singleton_of_ne_nil`, `fl_insertionSumList_has_list_schedule_of_ne_nil`, `fl_insertionSumList_has_sumTree_shape_of_ne_nil`, and `fl_insertionSumList_has_sumTree_eval_of_ne_nil`. The local nonnegative insertion choice is closed by `insertion_first_two_exact_sum_le_pair_sum_of_nonnegative`: for a nonnegative active list sorted by increasing absolute value, the first two entries minimize the next exact pair sum among admissible pairs. The exact running-error objective bridge is closed by `InsertionScheduleTree.exactEval_eq_leaves_sum`, `InsertionScheduleTree.exactEval_eq_of_leaves_perm`, `InsertionScheduleTree.exactMergeCost`, `InsertionScheduleTree.exactMergeCost_node_of_nonnegative`, `InsertionScheduleTree.toSumTree_runningErrorBudget_exactWithUnitRoundoff`, `InsertionScheduleTree.leafDepthWeights_weights_eq_leaves`, `InsertionScheduleTree.weightedLeafDepthCost_eq_weightedDepthPairsCost`, `InsertionScheduleTree.weightedLeafDepthCost_nonneg_of_leaves_nonnegative`, `InsertionScheduleTree.weightedLeafDepthCost_mono_startDepth_of_leaves_nonnegative`, `InsertionScheduleTree.weightedLeafDepthCost_leaf_pair_exchange_le`, `InsertionScheduleTree.weightedDepthPairsCost_pair_exchange_le`, and `InsertionScheduleTree.exactMergeCost_eq_weightedLeafDepthCost_of_leaves_nonnegative`, which rewrites the nonnegative objective as weighted external path length, exposes an explicit leaf-depth/weight list sum, and proves the core smaller-weight/deeper-position exchange inequality both bare and inside arbitrary explicit context. The existential and supplied-greedy global nonnegative optimal-merge theorems are closed by `InsertionScheduleTree.GreedyInsertionTree`, `InsertionScheduleTree.exists_greedyInsertionTree_weightedLeafDepthCost_le`, `InsertionScheduleTree.exists_greedyInsertionTree_exactMergeCost_le`, `InsertionScheduleTree.GreedyInsertionTree.weightedLeafDepthCost_le`, and `InsertionScheduleTree.GreedyInsertionTree.exactMergeCost_le`; `SumTree.runningErrorBudget_exactWithUnitRoundoff_greedyInsertion_le` closes the exact-arithmetic Algorithm 4.1-facing bridge for any supplied greedy insertion tree. The two displayed four-entry equivalence examples are closed by `insertionPowersFour_exact_order`, `fl_insertionPowersFour_eq_recursiveSum`, `insertionNearOneFour_exact_order`, and `fl_insertionNearOneFour_eq_pairwiseSum`, and inherit inverse-model running-error and one-signed exact-`gamma` relative-error bounds. The concrete exact-arithmetic source insertion trace and Algorithm 4.1 comparison are now closed by `insertionScheduleAfter_full_greedy_exactWithUnitRoundoff_of_ne_nil`, `fl_insertionSumList_has_greedy_schedule_exactWithUnitRoundoff_of_ne_nil`, and `fl_insertionSumList_exactWithUnitRoundoff_greedy_runningErrorBudget_le`. Remaining route choice: the literal arbitrary-`FPModel` computed-intermediate version needs additional model/order assumptions or an explicitly exact-arithmetic theorem surface. |
| C4.3 | pp. 90--91 | General Psum ordering, `O(n log n)` comparison claim, increasing-order optimality for nonnegative recursive summation, and broad heavy-cancellation ordering advice. | The finite permutation/order surface is present via `IncreasingMagnitudeOrder`, `StrictIncreasingMagnitudeOrder`, `DecreasingMagnitudeOrder`, `StrictDecreasingMagnitudeOrder`, `fl_recursiveSumInOrder`, and `sum_orderedInput_eq_sum`, with strict-to-weak bridges for the reusable predicates. Concrete list-level increasing/decreasing magnitude sorting is closed by `increasingAbsSort_sorted`, `increasingAbsSort_perm`, `increasingAbsSort_sum_eq`, `decreasingAbsSort_sorted`, `decreasingAbsSort_perm`, and `decreasingAbsSort_sum_eq`. The finite-vector bridge for `Fin n` inputs is closed by `increasingAbsSortVector`, `decreasingAbsSortVector`, `psumOrderVector`, and their sorted/permutation/greedy/sum theorems; `increasingAbsSortVector_recursiveRoundedPrefixBudget_exactWithUnitRoundoff_le`, `psumOrderVector_eq_increasingAbsSortVector_of_nonnegative`, and `psumOrderVector_recursiveRoundedPrefixBudget_exactWithUnitRoundoff_le` now give the finite-vector same-sign equivalence and budget comparison directly. The source-side list Psum generator and greedy invariant are closed by `psumSelect`, `psumSelect_min`, `psumSelect_perm`, `psumOrder`, `PsumGreedyOrderFrom.head_min`, `PsumGreedyOrderFrom.perm`, `psumOrder_perm`, and `psumOrder_greedyTrace`. The same-sign/nonnegative equivalence is closed in equality form by `psumSelect_le_of_nonnegative`, `IncreasingAbsList.sortedLE_of_nonnegative`, and `psumOrder_eq_increasingAbsSort_of_nonnegative`: Psum chooses a smallest available term and the resulting order is exactly the increasing-magnitude order for nonnegative inputs. The concrete scan-cost layer is closed by `psumSelectComparisonCost_eq_pred_length`, `psumOrderFromFuelComparisonCost_eq_triangular`, `psumOrderFromComparisonCost_eq_triangular`, and `psumOrderComparisonCost_eq_triangular`: this proves the current scan-based Psum implementation has exact triangular comparison count. The optimized comparison-cost surface is now represented by `PsumLogSearchTraceFrom`, `PsumLogSearchTraceFrom.greedyTrace`, `PsumLogSearchTraceFrom.perm`, `PsumLogSearchTraceFrom.cost_le_budget`, `psumOrder_logSearchTrace`, and `psumOrder_logSearchComparisonCost_le_mul_stepBudget`, which prove that a logarithmic-cost selector realizing the same Psum minimizer has total comparison budget bounded by `n * (2 * log2 (n+1) + 1)`. The ordered-neighbor selector foundation is closed by `PsumLowerNeighbor`, `PsumUpperNeighbor`, and `psumNeighborChoice_mem_and_min`: once a sorted/search structure exposes the predecessor and successor around `-acc`, choosing the closer one is proved to minimize the Psum objective over the active set. The sorted-list predecessor/successor/deletion adapter and log-cost trace are closed by `psumSortedLowerSearch_neighbor`, `psumSortedUpperSearch_neighbor`, `psumSortedNeighborSelect_mem_and_min`, `psumSortedNeighborSelect_erase_sorted_perm_length_min`, `PsumMinOrderFrom`, `psumSortedNeighborOrderFromFuel_minTrace`, `PsumSortedNeighborLogSearchTraceFrom.cost_le_budget`, and `psumSortedNeighborOrderFromFuel_logSearchTrace`. The concrete set-valued red-black-search specialization is closed by `psumRealCmp`, `PsumRBSet.toList_sortedLE`, `PsumRBSet.lowerBound_neighbor`, `PsumRBSet.upperBound_neighbor`, `PsumRBSet.neighborSelect_mem_and_min`, `PsumRBSet.depth_succ_le_stepBudget`, and `PsumRBSet.eraseValue_depth_succ_le_stepBudget`; this proves concrete lower/upper-bound search correctness, selector minimality, balance-backed logarithmic depth, and post-erase depth-budget preservation for distinct active keys. The duplicate-aware counted-list deletion bridge is closed by `psumCountEntriesExpand`, `psumCountEntriesEraseOne_perm`, and `psumCountEntriesEraseOne_length`: decrementing one counted occurrence realizes exactly one deletion in the expanded active-list view. The concrete counted red-black-map search layer is closed by `PsumCountRBMap.PositiveCounts`, `PsumCountRBMap.lowerBound_neighbor`, `PsumCountRBMap.upperBound_neighbor`, `PsumCountRBMap.neighborSelect_mem_and_min`, `PsumCountRBMap.eraseOne_entries_perm`, and `PsumCountRBMap.eraseOne_entries_length`: under positive stored multiplicities, key lower/upper-bound searches return predecessor/successor certificates over the expanded active list, the selector minimizes the Psum objective including duplicates, and the selected key has a duplicate-preserving expanded-list deletion bridge. The native counted-map implementation is now closed by `PsumCountRBMap.eraseOneNative_activeList_perm`, `PsumCountRBMap.eraseOneNative_activeList_length`, `PsumCountRBMap.eraseOneNative_preserves_positive`, `PsumCountRBMap.entryStep_of_stepNative`, `PsumCountRBMap.nativeOrderFrom_entryLogSearchTrace`, `PsumCountRBMap.nativeOrderFrom_minTrace`, `PsumCountRBMap.nativeOrderFrom_perm`, and `PsumCountRBMap.nativeOrderCostFrom_le_budget`: the executable native `RBMap` loop realizes the duplicate-aware deletion bridge, preserves positive multiplicities, composes into a counted-entry Psum trace, and satisfies the recursive logarithmic comparison budget. The nonnegative recursive-summation ordering claim is closed in exact a priori prefix-budget form by `recursiveExactPrefixBudgetFrom`, `recursiveExactPrefixBudget`, `recursiveExactPrefixBudgetFrom_insertIncreasingAbs_le_cons_of_nonnegative_sorted`, `increasingAbsSort_recursiveExactPrefixBudgetFrom_le`, `increasingAbsSort_recursiveExactPrefixBudget_le`, and `psumOrder_recursiveExactPrefixBudget_le`, and it now has an equation-(4.3)-style exact-arithmetic loop-budget bridge by `recursiveRoundedPrefixBudgetFrom`, `recursiveRoundedPrefixBudget`, `recursiveRoundedPrefixBudgetFrom_exactWithUnitRoundoff`, `recursiveRoundedPrefixBudget_exactWithUnitRoundoff`, `increasingAbsSort_recursiveRoundedPrefixBudget_exactWithUnitRoundoff_le`, and `psumOrder_recursiveRoundedPrefixBudget_exactWithUnitRoundoff_le`: replacing any supplied nonnegative list by increasing/Psum order cannot increase the exact prefix objective or the exact-arithmetic recursive-loop pre-rounding budget. The displayed example (4.5) is closed by `P91CancellationRounding`, `fl_p91Increasing_eq_zero`, `fl_p91Psum_eq_zero`, `fl_p91Decreasing_eq_one`, the three `p91*runningErrorBudget_eq` theorems, the heavy-cancellation ratio witnesses `p91Increasing_heavyCancellationAtLeast`, `p91Psum_heavyCancellationAtLeast`, and `p91Decreasing_heavyCancellationAtLeast`, and the conditional comparison theorems `heavyCancellation_exact_result_beats_zero_result` and `heavyCancellation_postCancellation_bound_beats_competitor` instantiated as `p91_decreasing_beats_increasing_under_heavyCancellation`, `p91_decreasing_beats_psum_under_heavyCancellation`, `p91_decreasing_postCancellation_bound_beats_increasing`, and `p91_decreasing_postCancellation_bound_beats_psum`. Remaining broad method-choice work is source-dependent and belongs to C4.11/Priest-style concrete post-cancellation and decreasing-order accuracy certificates. |
| C4.4 | pp. 92--93 | Error-free correction formula (4.7). | The rounded correction trace, finite round-to-even trace, exact-add split, exact-subtraction/Sterbenz bridges, and reusable `FastTwoSumFiniteCertificate` handoffs are closed by the listed C4.4 theorem family. The first rounded sum is unconditionally finite by `FastTwoSumFiniteCertificate.finite_s_unconditional`, and `FastTwoSumFiniteCertificate.of_error_obligations` reduces the future source theorem to representability of `a-s` and `(a+b)-s`. The true-local-error field has a same-lattice handoff by `FastTwoSumFiniteCertificate.finite_error_of_sameExponentScaledInteger`; the finite-normal source selector agrees with the total finite selector by `FloatingPointFormat.finiteRoundToEven_eq_finiteNormalRoundToEven_of_finiteNormalRange` and `FloatingPointFormat.finiteRoundToEvenOp_eq_finiteNormalRoundToEven_of_finiteNormalRange`; same-exponent endpoint selection is closed by `FloatingPointFormat.sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between` and `FloatingPointFormat.sourceRoundToEvenEvidence_sameExponent_mantissa_eq_or_succ_of_bracket`; and both aligned same-sign guard-word branches now close the required coefficient gap by `FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_coeffDiff_natAbs_lt_mantissaBound` and `FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_coeffDiff_natAbs_lt_mantissaBound`. `FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_alignedCoeff_lt_mantissaBound` closes the coefficient-fits same-sign normalized ordered-exponent branch; `FloatingPointFormat.finiteRoundToEvenOp_add_oppositeSign_sameExponent_error_finiteSystem` closes the opposite-sign same-exponent normalized branch; `FloatingPointFormat.finiteRoundToEvenOp_add_subnormal_error_finiteSystem` closes arbitrary-sign all-subnormal addition as an exact zero-error branch; and the two mixed operand-order finite-error wrappers close the same-sign mixed normal/subnormal coefficient-fits exact branch. `FloatingPointFormat.finiteRoundToEvenOp_add_neg_right_finiteSystem_eq_exact_of_sterbenzRatioCondition` and its commuted/error variants close the finite-system Sterbenz opposite-sign exact-add branch, including subnormal and mixed cases, once a ratio condition is available. Failed routes are also recorded by `correctionFormula_abs_order_not_imply_signed_sterbenz_exact_sum`, `correctionFormulaAbstractCounterexampleFPModel`, `correctionFormulaAbstractCounterexample_abs_order`, and `correctionFormulaAbstractCounterexample_not_exact`. Remaining target: prove `finiteRoundToEvenOp_add_error_finite_of_base2_abs_order_of_finiteNormalRange` for the remaining normalized different-exponent and mixed inexact-alignment cases, then use the acquired Shewchuk/Dekker split to derive the full finite base-2 all-signs TwoSum/FastTwoSum theorem deriving representability of `a-s` and `(a+b)-s` from the source assumptions. Original Dekker/Knuth/Linnainmaa theorem bodies remain unacquired. See `docs/CHAPTER04_C44_CORRECTION_FORMULA_BOTTLENECK.md` and `docs/CHAPTER04_PROOF_SOURCE_LEDGER.md`. |
| C4.4a | pp. 92--93 | Route-failure audit for equation (4.7). | `FloatingPointFormat.finiteNormalRange_not_enough_for_roundoff_error_finiteSystem` proves that finite-normal range alone is not enough to derive finite representability of the exact roundoff error: in the tiny binary `t = 2` format, `21/16` is in range and rounds to `3/2`, but the error `-3/16` is not finite representable. This closes the failed shortcut in the red-bottleneck checklist and forces the next theorem to use finite binary operand hypotheses. |
| C4.4b | pp. 92--93 | Coefficient-grid subdependency for equation (4.7). | `FloatingPointFormat.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound` proves the same-exponent scaled-integer handoff needed by the finite binary operand route: once the exact addition source and rounded endpoint are on a common signed exponent lattice and the coefficient gap fits in `t` digits, the exact error is finite representable. Remaining target: derive that common lattice and gap bound from the two finite binary operands and the adjacent round-to-even selector. |
| C4.4c | pp. 92--93 | FastTwoSum certificate finite-error handoff for equation (4.7). | `FastTwoSumFiniteCertificate.finite_error_of_sameExponentScaledInteger` lifts the same-exponent coefficient-grid bridge directly to the certificate field `finite_error`, proving `fmt.finiteSystem ((a+b)-fl(a+b))` from common-lattice source/round representations and a `t`-digit coefficient gap. Remaining target: derive those hypotheses from the finite binary operands and round-to-even adjacency, then combine with the separate `a-s` representability obligation. |
| C4.4d | pp. 92--93 | Aligned normalized operand-grid source case for equation (4.7). | `FloatingPointFormat.normalizedValue_add_sameSign_sameExponent_exists_scaledIntegerCoeff` proves the exact source-grid representation for same-sign, same-exponent normalized operands: `a+b` has coefficient `m+n` on the common exponent lattice with `m+n < 2*beta^t`. `FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_sameExponent_eq_exact_of_add_lt_mantissaBound` closes the exact aligned branch when `m+n < beta^t`. `FloatingPointFormat.binaryGuardQuotient_normalized_or_max_of_mantissaBound_le_of_lt_two_mul` dispatches the base-2 guard-word quotient either to a normalized `q,q+1` bracket or to the max-mantissa boundary branch. `FloatingPointFormat.binaryGuardCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_ceil` closes the pure binary lower/upper endpoint coefficient-gap arithmetic for the guard-word branch. `FloatingPointFormat.sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between` and `FloatingPointFormat.sourceRoundToEvenEvidence_sameExponent_mantissa_eq_or_succ_of_bracket` close the actual evidence-to-endpoint-index bridge once the same-exponent adjacent bracket is supplied. `FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem` and `FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem` close the positive and negative aligned same-sign guard-word branches through construction of the quotient brackets and finite representability of the local roundoff error. `FloatingPointFormat.finiteRoundToEvenOp_add_error_finite_of_sourceRoundToEvenEvidence` transfers these source finite-error witnesses to the concrete finite-normal add operation. Remaining target: extend the split to different exponents, opposite signs, and subnormal boundary cases required by the full finite binary theorem. |
| C4.4e | pp. 92--93 | Exponent-boundary guard-word branch for equation (4.7). | `FloatingPointFormat.binaryGuardQuotient_normalized_or_max_of_mantissaBound_le_of_lt_two_mul` identifies the max-mantissa boundary branch from the guard-word quotient. `FloatingPointFormat.normalizedValue_add_twoExponent_eq_beta_sq_scaledInteger` shifts the next-binade minimum endpoint onto the original source exponent lattice. `FloatingPointFormat.binaryGuardSource_between_boundaryEndpoints_positive` and `FloatingPointFormat.binaryGuardSource_between_boundaryEndpoints_negative` construct the positive and reversed negative brackets between `maxNormalMantissa` at exponent `e+1` and `minNormalMantissa` at exponent `e+2`. `FloatingPointFormat.binaryGuardBoundaryCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_boundary`, `FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_boundary_error_finiteSystem`, and `FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_boundary_error_finiteSystem` close finite representability of the local roundoff error for this boundary branch, and `FloatingPointFormat.finiteRoundToEvenOp_add_error_finite_of_sourceRoundToEvenEvidence` provides the finite-normal concrete-operation handoff. Remaining target: derive the remaining exponent-alignment, opposite-sign, and subnormal cases needed by the full rounded-add error theorem. |
| C4.4f | pp. 92--93 | Ordinary guard-word direct finite-error wrappers and coefficient-range dispatch for equation (4.7). | `FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem_of_normalizedQuotient` and `FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem_of_normalizedQuotient` prove the ordinary positive and negative aligned guard-word finite-error obligations directly from normalized quotient endpoints `q` and `q+1`, source round-to-even evidence, and the existing coefficient-gap lemma, without requiring a separate rounded-endpoint mantissa representation. `FloatingPointFormat.sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem_of_guardCoeffBounds` and `FloatingPointFormat.sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem_of_guardCoeffBounds` now compose those wrappers with the quotient dispatcher and the boundary finite-error wrappers, so a base-2 guard coefficient satisfying `beta^t <= k < 2*beta^t` directly yields finite local-error representability for either sign. Remaining target: derive such guard-coefficient hypotheses from the broader finite-binary operand case split. |
| C4.4g | pp. 92--93 | Mixed normal/subnormal one-guard branch for equation (4.7). | `FloatingPointFormat.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_guardCoeffBounds` rewrites a same-sign normalized-plus-subnormal source sum onto the `emin` subnormal lattice with coefficient `m * beta^(e-emin) + n`, then dispatches the binary one-guard range `beta^t <= k < 2*beta^t` to the existing positive/negative guard finite-error theorem. `FloatingPointFormat.finiteRoundToEvenOp_add_normalized_sameSign_subnormal_error_finiteSystem_of_guardCoeffBounds` and `FloatingPointFormat.finiteRoundToEvenOp_add_subnormal_sameSign_normalized_error_finiteSystem_of_guardCoeffBounds` transfer the source witness to both concrete finite-normal operand orders. Remaining target: derive the remaining alignment cases outside this one-guard range and the unresolved opposite-sign/magnitude splits needed by the full rounded-add error theorem. |
| C4.4h | pp. 92--93 | Exact-or-one-guard dispatch wrappers for equation (4.7). | `FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_alignedCoeff_lt_two_mul_mantissaBound`, `FloatingPointFormat.finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_alignedCoeff_lt_two_mul_mantissaBound`, `FloatingPointFormat.finiteRoundToEvenOp_add_normalized_sameSign_subnormal_error_finiteSystem_of_alignedCoeff_lt_two_mul_mantissaBound`, and `FloatingPointFormat.finiteRoundToEvenOp_add_subnormal_sameSign_normalized_error_finiteSystem_of_alignedCoeff_lt_two_mul_mantissaBound` combine the exact and one-guard same-sign branches under the single range hypothesis `alignedCoeff < 2*beta^t`. Remaining target: handle aligned coefficients at or above `2*beta^t` and the unresolved opposite-sign/magnitude cases needed by the full rounded-add error theorem. |
| C4.5 | pp. 93--94 | Kahan compensated summation bounds (4.8)--(4.9) and final-correction variant. | Algorithm 4.2's rounded trace is closed by `kahanStepTrace`, `kahanTrace`, and `fl_kahanSum`; the appended `s = s + e` variant is closed by `fl_kahanFinalCorrectedSum`. The local bridge from the correction formula into the Kahan loop is closed by `kahanStepTrace_correctionFormulaTrace`, `kahanStepTrace_compensated_total_eq_of_exact_y_and_correction`, and `kahanStep_compensated_total_eq_of_exact_y_and_correction`: each step uses exactly equation (4.7)'s correction trace, and exact `y` plus exact local correction preserves the compensated total. The prefix, full-state, and public returned-sum/correction invariants are now closed by `kahanPrefixState_compensated_total_eq_sum_of_exact_steps`, `fl_kahanState_compensated_total_eq_sum_of_exact_steps`, and `fl_kahanSum_add_correction_eq_sum_of_exact_steps`: if every processed step satisfies those local exactness hypotheses, the compensated total `s + e` equals the exact prefix/final sum. The final-correction exactness corollary `fl_kahanFinalCorrectedSum_eq_sum_of_exact_steps_and_final_add` shows that an exact appended `s+e` add returns the exact source sum under the same step hypotheses. The exact-arithmetic sanity surface is closed by `fl_kahanState_exactWithUnitRoundoff`, `fl_kahanSum_exactWithUnitRoundoff`, `fl_kahanCorrection_exactWithUnitRoundoff`, and `fl_kahanFinalCorrectedSum_exactWithUnitRoundoff`. The backward-to-forward algebra behind the source's transition from (4.8) to (4.9) is closed by `kahan_backward_error_forward_bound_core`, `fl_kahanSum_forward_error_bound_of_backward`, `fl_kahanSum_relError_le_of_backward_oneSigned`, `fl_kahanFinalCorrectedSum_forward_error_bound_of_backward`, and `fl_kahanFinalCorrectedSum_relError_le_of_backward_oneSigned`. Remaining target: use the Knuth/Kahan/Goldberg/Kahan proof route to instantiate the actual backward-error witnesses, the concrete (4.9) constant, and the stronger final-correction bound. |
| C4.6 | p. 94 | Alternative compensated summation and equation (4.10). | The separate-correction algorithm trace is closed by `alternativeCompensatedTrace`, `alternativeCompensatedCorrections`, and `fl_alternativeCompensatedSum`. The local bridge from the correction formula into the alternative trace is closed by `alternativeCompensatedStepTrace_correctionFormulaTrace` and `alternativeCompensatedStepTrace_main_plus_correction_eq_of_correction`: each stored local correction is exactly equation (4.7)'s correction trace for the current main sum and input, and exact local correction gives `new main sum + stored correction = old main sum + x_i`. The prefix and final exact-correction algebra are closed by `alternativeCompensatedPrefixSum_add_corrections_eq_sum_of_exact_steps`, `fl_alternativeCompensatedMainSum_add_exact_corrections_eq_sum_of_exact_steps`, and `fl_alternativeCompensatedSum_eq_sum_of_exact_steps_and_exact_correction_sum`: exact local corrections make `main sum + exact stored-correction sum` equal the exact source sum, and exact global-correction accumulation plus exact final add makes the final returned value exact. The exact-arithmetic sanity surface is closed by `fl_alternativeCompensatedMainSum_exactWithUnitRoundoff`, `alternativeCompensatedCorrections_exactWithUnitRoundoff`, `fl_alternativeCompensatedGlobalCorrection_exactWithUnitRoundoff`, and `fl_alternativeCompensatedSum_exactWithUnitRoundoff`. The conditional backward-to-forward and one-signed relative-error bridge for an equation-(4.10)-style perturbation representation is closed by `fl_alternativeCompensatedSum_forward_error_bound_of_backward` and `fl_alternativeCompensatedSum_relError_le_of_backward_oneSigned`. Remaining target: acquire Kielbasinski/Neumaier/Jankowski proof sources and prove the actual equation (4.10) perturbation bound under its `nu < 0.1` regime. |
| C4.7 | pp. 94--95 | No-guard failure and Kahan's machine-dependent modified compensated algorithm. | The local no-guard failure of correction-formula exactness is closed by `NoGuardCorrectionFormulaTrace.model`, `noGuardCorrectionFormulaCounterexample_model`, and `noGuardCorrectionFormulaCounterexample_not_exact`. The ordinary no-guard Kahan trace is closed by `kahanNoGuardStepTrace`, `kahanNoGuardTrace`, and final-state wrappers over `NoGuardFPModel`; the concrete two-term witness is closed by `kahanNoGuardCounterexampleModel`, `fl_kahanNoGuardCounterexampleState_eq`, `fl_kahanNoGuardCounterexampleSum_eq`, `kahanNoGuardCounterexample_exactSum_eq`, and `kahanNoGuardCounterexample_relError_eq_one`, proving a full compensated run with relative error exactly one under the no-guard model. The modified correction trace is closed by `kahanModifiedNoGuardStepTrace` and final-state wrappers over `NoGuardFPModel`, and its exact-arithmetic sanity surface is closed by `kahanModifiedNoGuardStep_exactWithUnitRoundoff`, `fl_kahanModifiedNoGuardState_exactWithUnitRoundoff`, `fl_kahanModifiedNoGuardSum_exactWithUnitRoundoff`, and `fl_kahanModifiedNoGuardCorrection_exactWithUnitRoundoff`. Remaining target: prove or ledger the machine-dependent Kahan 1973 guarantee assumptions for the modified algorithm. |
| C4.8 | pp. 96--97 | Priest doubly compensated summation near-full-precision guarantee. | Algorithm 4.3's rounded trace is closed by `priestStepTrace`, `priestTrace`, and `fl_priestSum`, with `priestStrictlySortedByDecreasingAbs` and `priestSortedByDecreasingAbs_of_strict` recording the source's strict ordering precondition. The exact-arithmetic sanity surface is closed by `fl_priestState_exactWithUnitRoundoff`, `fl_priestSum_exactWithUnitRoundoff`, and `fl_priestCorrection_exactWithUnitRoundoff`. Remaining target: acquire Priest proof source and define the t-digit base-beta finite-format assumptions needed for the guarantee. |
| C4.9 | pp. 97--98 | Accumulator and distillation algorithms. | Source-level accumulator and distillation traces are now present in `AccumulatorSum.lean`. The source's final decreasing-absolute-value accumulator summation surface is closed by `fl_accumulatorSum_eq_recursive_final_state` and `fl_accumulatorSum_uses_decreasing_abs_order`: the final phase is recursive summation of the final accumulator bank in the supplied order, and the supplied order can be required to satisfy `DecreasingAbsAccumulatorOrder`. The concrete exact-arithmetic no-overflow sanity path is closed by `accumulatorNeverOverflow`, `fl_accumulatorState_neverOverflow_zero_exactWithUnitRoundoff`, `fl_accumulatorState_neverOverflow_of_ne_zero_exactWithUnitRoundoff`, and `fl_accumulatorSum_neverOverflow_exactWithUnitRoundoff`: for any finite accumulator bank and identity final order, the lowest accumulator contains the exact source sum, every higher accumulator remains zero, and the full method returns the exact source sum. The one-level theorem `fl_accumulatorSum_singleLevel_neverOverflow_exactWithUnitRoundoff` is retained as a specialization. The abstract distillation sum-preservation surface is now closed by `distillationInitialState_sum_eq`, `distillationTrace_finalState_sum_eq`, and `distillationTrace_finalState_sum_eq_initial`, and its termination predicate has the checked relative-error theorem `distillationTrace_finalComponent_relError_le` plus the absolute-error consequence `distillationTrace_finalComponent_abs_error_le`, so any terminating trace with nonzero exact sum satisfies `|z - sum x| <= u * |sum x|`. Remaining targets: instantiate concrete Wolfe/Malcolm/Ross machine overflow/interval assumptions, prove Malcolm's finite-machine relative-error order-`u` guarantee, choose a concrete distillation transform from the cited sources, and formalize the average-runtime lower/order claim if it is to be theorem-bearing. |
| C4.10 | pp. 98--99 | Statistical mean-square estimates and Table 4.1. | The generic finite-probability running-error kernel is closed by `statisticalWeightedRoundingErrorSum`, `StatisticalRoundingErrorModel.expectation_weighted_sum_eq_zero`, `StatisticalRoundingErrorModel.expectation_weighted_sum_sq_eq_sum_weight_sq_second_moments`, `StatisticalRoundingErrorModel.expectation_weighted_sum_sq_le_weight_sq_mul_unit_sq`, and `StatisticalRoundingErrorModel.rms_weighted_sum_le_sqrt_weight_sq_mul_unit`: deterministic intermediate-sum weights multiplying zero-mean pairwise-uncorrelated addition errors have zero mean, mean square equal to the weighted sum of local second moments, and RMS at most `sqrt (sum_i w_i^2) * u` under the local second-moment bound. The Algorithm 4.1 tree-weight bridge is closed by `SumTree.computedInternalSums`, `SumTree.computedInternalSums_length_eq_numAdds`, `SumTree.computedInternalSums_abs_sum_eq_runningErrorBudget`, `SumTree.statisticalRunningErrorContribution`, `SumTree.statisticalRunningErrorContribution_expectation_eq_zero`, `SumTree.statisticalRunningErrorContribution_expectation_sq_eq_sum`, `SumTree.statisticalRunningErrorContribution_expectation_sq_le`, and `SumTree.statisticalRunningErrorContribution_rms_le`, so the statistical weights are exactly the computed internal sums from equations (4.2)--(4.3). The printed Table 4.1 constants/exponents and immediate rankings are closed by `Table41Distribution`, `Table41Method`, `table41MeanSquareConstant`, `table41NExponent`, `table41MeanSquareEstimate`, `table41_recursive_constants_rank_uniform`, `table41_recursive_constants_rank_exponential`, `table41_insertion_constant_lt_pairwise_uniform`, `table41_insertion_constant_lt_pairwise_exponential`, `table41_recursive_exponents_eq_three`, and `table41_insertion_pairwise_exponents_eq_two`. The full displayed estimate rankings are now also closed by `table41MeanSquareScale_pos`, `table41_recursive_estimates_rank_uniform`, `table41_recursive_estimates_rank_exponential`, `table41_insertion_estimate_lt_pairwise_uniform`, and `table41_insertion_estimate_lt_pairwise_exponential`, which lift the constant comparisons through the positive common scale. Remaining target: derive the Robertazzi--Schwartz constants from their distributional assumptions for the five methods. |
| C4.11 | p. 99 | Method-choice guarantees involving higher precision, compensated summation, insertion minimization, and heavy cancellation. | The one-signed absolute-to-relative reduction is closed in exact `gamma` form for Algorithm 4.1 trees, recursive summation, pairwise summation, and the higher-precision recursive-sum-then-round trace. The small-`u` linearized one-signed bound is closed for generic Algorithm 4.1 trees by `gamma_le_two_mul_n_u_of_nu_le_half` and `SumTree.relError_le_two_mul_n_minus_one_u_of_oneSigned`: if `(n-1)u <= 1/2`, relative error is at most `2(n-1)u`. The source-shaped `nu` advice is closed for generic Algorithm 4.1 trees by `gamma_pred_le_n_mul_u_of_n_mul_pred_u_le_one` and `SumTree.relError_le_n_mul_u_of_oneSigned`: for nonempty one-signed data with nonzero exact sum, `gammaValid (n-1)`, and `n*(n-1)*u <= 1`, relative error is at most `n*u`. Direct recursive and pairwise method surfaces are closed by `recursiveSum_relError_le_n_mul_u_of_oneSigned`, `pairwiseSum_relError_le_pow_two_mul_u_of_oneSigned`, and `pairwiseCarrySum_relError_le_n_mul_u_of_oneSigned`. The pairwise large-`n` advice now has an explicit depth comparison by `pairwiseCarryTree_depth_le_linear`: the carry-forward pairwise depth `ceil(log2 n)` is bounded by the generic `n - 1` depth. The higher-precision recursive-sum-then-round trace is closed by `fl_higherPrecisionRecursiveSum`, its exact high-precision plus identity final-rounding sanity theorem is closed by `fl_higherPrecisionRecursiveSum_exactWithUnitRoundoff_id`, the displayed mixed-precision two-term error composition is closed by `fl_higherPrecisionRecursiveSum_abs_error_le_of_high_bound`, `fl_higherPrecisionRecursiveSum_abs_error_le_nu_sq`, and `fl_higherPrecisionRecursiveSum_abs_error_le_gamma`, and the one-signed relative lift is closed by `fl_higherPrecisionRecursiveSum_relError_le_of_high_bound_oneSigned` plus `fl_higherPrecisionRecursiveSum_relError_le_gamma_oneSigned`. The source's heavy-cancellation ratio now has the reusable predicate `HeavyCancellationAtLeast`; `heavyCancellation_exact_result_beats_inexact_result` gives the general conditional relative-error comparison for equal-sum orderings when one computed result is exact and the competitor is inexact, while `heavyCancellation_exact_result_beats_zero_result` retains the p. 91 zero-collapse specialization. The checkable post-cancellation route is closed by `relError_le_of_abs_sub_le_mul_abs` and `heavyCancellation_postCancellation_bound_beats_competitor`, with p. 91 instantiated by `p91_decreasing_postCancellation_bound_beats_increasing` and `p91_decreasing_postCancellation_bound_beats_psum`. Remaining targets are Priest's finite-format decreasing-order higher-precision theorem, the doubly compensated relative-error guarantee, compensated perfect relative accuracy, arbitrary-`FPModel` computed-bound insertion minimization if required, and deriving concrete post-cancellation certificates for broad finite-format decreasing-order computations. |
| C4.12 | pp. 100--102 | Problems 4.1--4.9. | Problem 4.1 is closed by the summation condition-number surface in `Summation.lean`: the componentwise perturbation model, sharp closed form, lower bound `C(x) >= 1`, and `C(x)=1` iff one-signed/no-cancellation characterization are all proved. Problem 4.2 is now closed for the concrete IEEE-double `t = 53` route in `WilkinsonAttainability.lean`: finite input representability, arbitrary rounded trace, realized-error defect identity, first-order factor-4 near-attainment, and exact-gamma factor-8 near-attainment under the explicit denominator condition are proved; a fully generic arbitrary-precision `t`-digit version is not claimed. Problem 4.3 is closed in `RecursiveSum.lean`: the exact recursive `theta/gamma` representation, weighted absolute-error bound, displayed indexed bound, decreasing-weight facts, adjacent-exchange certificate, and global increasing-absolute-value minimizer over all finite permutations are proved. Problem 4.4 is closed in `Problem44SixTerm.lean`: the absorbing-large-`M` source model exhaustively proves the six-term recursive-summation outputs are exactly `0,1,...,10`. Problem 4.5 is closed in `PlusMinusSum.lean`: the exact split, separated one-signed conditioning advantage, concrete recursive error bound, and final-cancellation relative-error disadvantage are proved. Problem 4.6 is closed in `AitkenDenominator.lean`: the exact denominator identities, all three rounded-route bounds, and the formal recommendation of the first-difference expression are proved at the standard-model parenthesization level with exact scaling by `2`. Problem 4.7 is closed in `LogExpProduct.lean`: exact identity, composed product perturbation, final log absolute-error formula, and relative-error denominator are proved with an explicit positive-log-input side condition. Problem 4.8 is closed in `GridPoints.lean`: the exact convex identity, stored-step representation-error amplification for recurrence/direct routes, and rounded bounds for all three routes are proved. Problem 4.9 is adjacent to the existing Kahan/Priest trace surfaces. Remaining missing theorem surfaces: Priest's smallest-`n` compensated-summation research problem including the displayed IEEE single counterexample, plus the optional generic `t`-digit lift of Problem 4.2 if exact source generality is required. |

## Proof-Source Needs

The excerpt gives complete local derivations for Algorithm 4.1 equations
(4.1)--(4.4) once the inverse operation model is available, and those rows are
closed locally.  The compensated and doubly compensated results are
citation-only or proof-sketch level in this excerpt.  Before hard proof work on
those rows, inspect the cited primary sources:

- Dekker 1971, Theorem 4.7; Knuth 1981, Theorem C; Linnainmaa 1974, Theorem 3
  for equation (4.7).
- Knuth 1981, Exercise 19; Goldberg 1991; Kahan 1972/1973 for equations
  (4.8)--(4.9) and the final-correction variant.
- Kielbasinski 1973; Neumaier 1974; Jankowski--Smoktunowicz--Wozniakowski 1983
  for equation (4.10).
- Priest 1992, Section 4.1 and pp. 62--69 for Algorithm 4.3 and doubly
  compensated/distillation results.
- Wolfe 1964, Malcolm 1971, Ross 1965, Kahan 1987, Bohlender 1977,
  Leuprecht--Oberaigner 1982, Pichat 1972, and Priest 1992 pp. 66--69 for
  concrete accumulator and distillation transforms, machine assumptions,
  runtime claims, and error guarantees.
- Robertazzi--Schwartz 1988 for the statistical estimates in Table 4.1.
- Wilkinson 1963, p. 19 for the Problem 4.2 attainability construction.
- Priest 1992, pp. 61--62 for the Problem 4.9 compensated-summation research
  problem and displayed counterexample family.

## Audit Verdict

The answer to "has `Chapter04_full.pdf` been fully and faithfully end-to-end
formalized?" is **no**.  The foundational Algorithm 4.1 summation-tree analysis
is now substantially closed, including the source-shaped running-error identity
and bound, the source-shaped arbitrary-length carry-forward pairwise process,
the scalar arbitrary-length padded pairwise bound, the displayed six-term
pairwise schedule, the two displayed insertion special-case examples with
their inherited running-error and one-signed bounds, the general insertion
active-list loop and sortedness invariant, the exact insertion merge-cost
bridge to the Algorithm 4.1 running-error budget under exact arithmetic and
its nonnegative weighted-path-length form,
explicit recursive-summation
permutation order predicates with exact-sum preservation, the p. 91 ordering
example (4.5), the correction-formula trace, the Kahan Algorithm 4.2 trace and
final-correction variant, the alternative compensated trace, Kahan's modified
no-guard trace, and the Priest Algorithm 4.3
trace, plus the source-level accumulator cascade and distillation
invariant/termination traces, plus the one-signed exact-`gamma` relative-error
corollary for the closed Algorithm 4.1 summation surfaces.  Full Chapter 4
closure still
requires the open rows
above, including Problems 4.1--4.9.  The highest-priority theorem-bearing gaps
remain the red C4.4 correction-formula route, the compensated-summation bounds
C4.5--C4.6, and the now-explicit problem-set rows on pp. 100--102.
