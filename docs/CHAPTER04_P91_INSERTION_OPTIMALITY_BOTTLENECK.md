# Chapter 4 p. 91 Insertion-Optimality Bottleneck

## Source Target

- Source: `references/Chapter04_full.pdf`, p. 91, Section 4.2.
- Repeated source echo: p. 99, Section 4.6, advice item 3.
- Claim: for nonnegative inputs, insertion summation minimizes the Chapter 4
  running-error bound (4.3) over all instances of Algorithm 4.1.

## Active Theorem Family

The core exact-combinatorial Huffman/optimal-merge statement over list-shaped
summation trees is now present in existential form:

```lean
theorem InsertionScheduleTree.exists_greedyInsertionTree_exactMergeCost_le
    (tree : InsertionScheduleTree)
    (hnonneg : ∀ x ∈ tree.leaves, 0 ≤ x) :
    ∃ greedyTree : InsertionScheduleTree,
      GreedyInsertionTree greedyTree ∧
        greedyTree.leaves.Perm tree.leaves ∧
          greedyTree.exactMergeCost ≤ tree.exactMergeCost
```

The arbitrary supplied-greedy optimality adapter is now closed:

```lean
theorem InsertionScheduleTree.GreedyInsertionTree.exactMergeCost_le
    (hgreedy : GreedyInsertionTree greedy)
    (hperm : greedy.leaves.Perm other.leaves)
    (hnonneg : ∀ x ∈ greedy.leaves, 0 ≤ x) :
    greedy.exactMergeCost ≤ other.exactMergeCost
```

The exact-arithmetic Algorithm 4.1-facing endpoint is also closed:

```lean
theorem SumTree.runningErrorBudget_exactWithUnitRoundoff_greedyInsertion_le
    (u0 : ℝ) (hu0 : 0 ≤ u0)
    (insertion : InsertionScheduleTree)
    (other : SumTree n) (v : Fin n → ℝ)
    (hv : ∀ i, 0 ≤ v i)
    (hperm : insertion.leaves.Perm (other.toInsertionScheduleTree v).leaves)
    (hgreedy : GreedyInsertionTree insertion) :
    insertion.exactMergeCost ≤
      SumTree.runningErrorBudget (FPModel.exactWithUnitRoundoff u0 hu0) other v
```

The concrete source-level insertion trace now realizes the greedy tree
predicate and composes with the exact-arithmetic Algorithm 4.1 endpoint:

```lean
theorem insertionScheduleAfter_full_greedy_exactWithUnitRoundoff_of_ne_nil
    (u0 : ℝ) (hu0 : 0 ≤ u0) :
    ∀ {xs : List ℝ} (_ : xs ≠ [])
      (_ : IncreasingAbsList xs)
      (_ : ∀ x ∈ xs, 0 ≤ x)
      {item : InsertionScheduleItem
        (FPModel.exactWithUnitRoundoff u0 hu0)},
      insertionScheduleAfter (FPModel.exactWithUnitRoundoff u0 hu0)
        xs.length
        (initialInsertionScheduleItems
          (FPModel.exactWithUnitRoundoff u0 hu0) xs) = [item] →
      item.tree.GreedyInsertionTree

theorem fl_insertionSumList_exactWithUnitRoundoff_greedy_runningErrorBudget_le
    (u0 : ℝ) (hu0 : 0 ≤ u0)
    {xs : List ℝ} (hne : xs ≠ [])
    (hsorted : IncreasingAbsList xs)
    (other : SumTree n) (v : Fin n → ℝ)
    (hv : ∀ i, 0 ≤ v i)
    (hperm : xs.Perm (SumTree.toInsertionScheduleTree other v).leaves) :
    ∃ insertion : InsertionScheduleTree,
      insertion.leaves.Perm xs ∧
        insertion.GreedyInsertionTree ∧
          insertion.eval (FPModel.exactWithUnitRoundoff u0 hu0) =
            fl_insertionSumList
              (FPModel.exactWithUnitRoundoff u0 hu0) xs ∧
          insertion.exactMergeCost ≤
            SumTree.runningErrorBudget
              (FPModel.exactWithUnitRoundoff u0 hu0) other v
```

There is also a route choice for the literal source wording: equation (4.3)
contains computed intermediate quantities.  The current closed bridge is for
`FPModel.exactWithUnitRoundoff`, where computed intermediates equal exact
intermediate sums.  A theorem for arbitrary floating-point `FPModel` would need
extra rounding-order/nonnegativity assumptions not currently supplied by the
basic model.

## Dependency Checklist

| Dependency | Status | Evidence / next Lean target |
| --- | --- | --- |
| Running-error bound (4.3) for arbitrary Algorithm 4.1 `SumTree`s | available-local | `SumTree.runningErrorBudget`, `SumTree.running_error_sum_bound_from_inverse_models` |
| List-shaped insertion schedule with leaves permuting the source input | available-local | `fl_insertionSumList_has_list_schedule_of_ne_nil`, `fl_insertionSumList_has_sumTree_eval_of_ne_nil` |
| Nonnegative exact merge-cost objective equals weighted external path length | available-local | `InsertionScheduleTree.exactMergeCost_eq_weightedLeafDepthCost_of_leaves_nonnegative` |
| Explicit leaf-depth/weight rearrangement surface | available-local | `InsertionScheduleTree.leafDepthWeights`, `InsertionScheduleTree.weightedDepthPairsCost`, `InsertionScheduleTree.weightedLeafDepthCost_eq_weightedDepthPairsCost`, `InsertionScheduleTree.leaves_eq_of_leafDepthWeights_pair_display`, and `InsertionScheduleTree.leaves_eq_of_leafDepthWeights_single_display` recover the plain leaf context from displayed entries in the leaf-depth list. |
| Smaller weight at no shallower depth exchange | available-local | `InsertionScheduleTree.weightedLeafDepthCost_leaf_pair_exchange_le`, `InsertionScheduleTree.weightedDepthPairsCost_pair_exchange_le`, `InsertionScheduleTree.weightedDepthPairsCost_pair_exchange_separated_le` |
| Sibling contraction identity for Huffman induction | available-local | `InsertionScheduleTree.weightedLeafDepthCost_node_leaf_leaf_eq_contract`, `InsertionScheduleTree.weightedDepthPairsCost_pair_contract_eq` |
| Arbitrary Algorithm 4.1 materialization into the weighted objective | available-local | `SumTree.toInsertionScheduleTree`, `SumTree.runningErrorBudget_exactWithUnitRoundoff_eq_weightedLeafDepthCost_of_nonnegative` |
| Deepest sibling-leaf existence for every nontrivial binary schedule tree | available-local | `InsertionScheduleTree.maxLeafDepth`, `InsertionScheduleTree.depth_le_maxLeafDepth`, `InsertionScheduleTree.succ_depth_le_maxLeafDepth_of_one_lt_leafCount`, `InsertionScheduleTree.leafDepthWeights_depth_le_maxLeafDepth`, `InsertionScheduleTree.two_smallest_depths_le_deepest_parent_context`, `InsertionScheduleTree.exists_deepest_sibling_leaf_pair` |
| Pair-list no-op branch for already arranged cases | available-local | `InsertionScheduleTree.weightedDepthPairsCost_of_perm_le_and_weights_perm` |
| One-slot overlap exchange support | available-local | `InsertionScheduleTree.weightedDepthPairsCost_pair_exchange_separated_of_perm_le_and_weights_perm`, `InsertionScheduleTree.weightedDepthPairsCost_pair_exchange_of_context_min_le_and_weights_perm` |
| Two-slot deepest-pair weighted exchange core | available-local | `InsertionScheduleTree.weightedDepthPairsCost_two_pair_exchange_separated_le`, `InsertionScheduleTree.weightedDepthPairsCost_two_pair_exchange_separated_of_perm_le`, `InsertionScheduleTree.weightedDepthPairsCost_two_pair_exchange_of_context_min_le` |
| Finite two-smallest weight locator for explicit leaf-depth lists | available-local | `InsertionScheduleTree.exists_two_smallest_weight_decomposition`, `InsertionScheduleTree.exists_two_smallest_weight_decomposition_components` |
| Finite occurrence locators for classifier case splits | available-local | `InsertionScheduleTree.exists_selected_relative_to_adjacent_pair`, `InsertionScheduleTree.exists_two_selected_slots_of_perm_cons_cons`, `InsertionScheduleTree.exists_second_position_of_first_before_adjacent_pair`, `InsertionScheduleTree.exists_second_position_of_first_after_adjacent_pair` |
| Located deepest-pair exchange preserves leaf-weight multiset | available-local | `InsertionScheduleTree.weightedDepthPairsCost_two_pair_exchange_of_context_min_le_and_weights_perm` |
| Nondegenerate two-smallest/deepest-pair instantiation | available-local | `InsertionScheduleTree.weightedDepthPairsCost_two_pair_exchange_of_two_smallest_decomposition_le_and_weights_perm` |
| All one-slot two-smallest/deepest overlap orientations | available-local | `InsertionScheduleTree.weightedDepthPairsCost_pair_exchange_of_left_deepest_two_smallest_decomposition_le_and_weights_perm`, `InsertionScheduleTree.weightedDepthPairsCost_pair_exchange_of_right_deepest_two_smallest_decomposition_le_and_weights_perm`, `InsertionScheduleTree.weightedDepthPairsCost_pair_exchange_of_left_deepest_second_two_smallest_decomposition_le_and_weights_perm`, `InsertionScheduleTree.weightedDepthPairsCost_pair_exchange_of_right_deepest_second_two_smallest_decomposition_le_and_weights_perm` |
| Pair-list dispatcher for moving two-smallest weights to deepest slots | available-local | `InsertionScheduleTree.TwoSmallestDeepestExchangeBranch`, `InsertionScheduleTree.weightedDepthPairsCost_two_smallest_deepest_exchange_branch_le_and_weights_perm` |
| Conditional dispatcher output to realized schedule-tree bridge | available-local | `InsertionScheduleTree.weightedLeafDepthCost_two_smallest_deepest_exchange_branch_realized_le_and_leaves_perm` |
| Same-shape relabeling realization for exact depth order | available-local | `InsertionScheduleTree.relabelLeaves`, `InsertionScheduleTree.relabelLeaves_leaves_eq`, `InsertionScheduleTree.relabelLeaves_leafDepthWeights_eq_zip`, `InsertionScheduleTree.relabelLeaves_leafDepthWeights_eq_pairs_of_depths_eq`, `InsertionScheduleTree.relabelLeaves_leaves_eq_pairs_of_depths_eq`, `InsertionScheduleTree.exists_relabelLeaves_leafDepthWeights_eq_of_depths_eq` |
| Same-depth dispatcher output to actual schedule tree | available-local | `InsertionScheduleTree.exists_relabelLeaves_for_two_smallest_deepest_exchange_branch_of_depths_eq` |
| Contraction-aware dispatcher realization | available-local | `InsertionScheduleTree.exists_relabelLeaves_contract_for_two_smallest_deepest_exchange_branch_of_context_lengths` packages a branch output, same-depth relabeling, same-length contraction context, resulting `SiblingLeafContract`, cost monotonicity, leaf permutation, and realized leaf-depth list. |
| Outer nonoverlap contraction-normalization branches | available-local | `InsertionScheduleTree.exists_relabelLeaves_contract_for_two_pair_exchange_after_contracted_pair`, `InsertionScheduleTree.exists_relabelLeaves_contract_for_two_pair_exchange_reverse_after_contracted_pair`, `InsertionScheduleTree.exists_relabelLeaves_contract_for_two_pair_exchange_before_contracted_pair`, and `InsertionScheduleTree.exists_relabelLeaves_contract_for_two_pair_exchange_reverse_before_contracted_pair` close the branches where the old contracted sibling pair is wholly before or wholly after both selected slots, in both selected-slot orders. |
| Mixed nonoverlap contraction-normalization branches | available-local | `InsertionScheduleTree.exists_relabelLeaves_contract_for_two_pair_exchange_around_contracted_pair` and `InsertionScheduleTree.exists_relabelLeaves_contract_for_two_pair_exchange_reverse_around_contracted_pair` close the branches where one selected smallest slot lies on each side of the old contracted sibling pair. |
| Overlap/no-op contraction-normalization branches | available-local | `InsertionScheduleTree.exists_relabelLeaves_contract_for_left_deepest_first_smallest_after_contracted_pair`, `InsertionScheduleTree.exists_relabelLeaves_contract_for_right_deepest_first_smallest_after_contracted_pair`, `InsertionScheduleTree.exists_relabelLeaves_contract_for_left_deepest_second_smallest_after_contracted_pair`, `InsertionScheduleTree.exists_relabelLeaves_contract_for_right_deepest_second_smallest_after_contracted_pair`, `InsertionScheduleTree.exists_relabelLeaves_contract_for_left_deepest_first_smallest_before_contracted_pair`, `InsertionScheduleTree.exists_relabelLeaves_contract_for_right_deepest_first_smallest_before_contracted_pair`, `InsertionScheduleTree.exists_relabelLeaves_contract_for_left_deepest_second_smallest_before_contracted_pair`, `InsertionScheduleTree.exists_relabelLeaves_contract_for_right_deepest_second_smallest_before_contracted_pair`, and `InsertionScheduleTree.exists_relabelLeaves_contract_for_deepest_pair_noop` close the one-slot-overlap branches on either side of the old contracted pair plus the already-normalized sibling-pair branch. |
| Combined nonoverlap occurrence-to-contraction classifiers | available-local | `InsertionScheduleTree.exists_relabelLeaves_contract_for_first_before_contracted_pair_nonoverlap_anywhere` and `InsertionScheduleTree.exists_relabelLeaves_contract_for_first_after_contracted_pair_nonoverlap_anywhere` combine the second-position locators with the contraction-aware nonoverlap branch package. |
| Combined first-outside overlap/nonoverlap contraction classifiers | available-local | `InsertionScheduleTree.exists_relabelLeaves_contract_for_first_before_contracted_pair_anywhere` and `InsertionScheduleTree.exists_relabelLeaves_contract_for_first_after_contracted_pair_anywhere` additionally handle the cases where the second selected smallest entry is one of the old contracted siblings, returning the resulting `SiblingLeafContract` in either sibling orientation. |
| Combined first-inside overlap/no-op contraction classifiers | available-local | `InsertionScheduleTree.exists_relabelLeaves_contract_for_left_deepest_first_two_smallest_anywhere` and `InsertionScheduleTree.exists_relabelLeaves_contract_for_right_deepest_first_two_smallest_anywhere` handle the cases where the first selected smallest entry is already one of the old contracted siblings and the second selected entry is before the pair, after the pair, or the other old sibling. |
| Fixed-context arbitrary occurrence-to-contraction dispatcher | available-local | `InsertionScheduleTree.exists_relabelLeaves_contract_for_two_smallest_deepest_pair_anywhere_of_occurrence_classifiers` combines the selected-relative-to-adjacent-pair split with four fixed-context occurrence continuations, preserving one shared old sibling-pair context. |
| Fixed-context occurrence-to-contraction continuations | available-local | `InsertionScheduleTree.exists_relabelLeaves_contract_for_first_before_contracted_pair_anywhere_of_context`, `InsertionScheduleTree.exists_relabelLeaves_contract_for_first_after_contracted_pair_anywhere_of_context`, `InsertionScheduleTree.exists_relabelLeaves_contract_for_left_deepest_first_two_smallest_anywhere_of_context`, and `InsertionScheduleTree.exists_relabelLeaves_contract_for_right_deepest_first_two_smallest_anywhere_of_context` supply the four shared-context continuations required by the arbitrary occurrence dispatcher. |
| Explicit-context normalized two-smallest/deepest contraction | available-local | `InsertionScheduleTree.exists_relabelLeaves_contract_for_two_smallest_deepest_pair_anywhere_of_context` composes the four fixed-context occurrence continuations when a deepest sibling display and same-length branch bridge are already supplied, avoiding any reopening of the structural contraction-context existential. |
| Full normalized two-smallest/deepest sibling contraction | available-local | `InsertionScheduleTree.exists_relabelLeaves_contract_for_two_smallest_deepest_pair_anywhere` obtains one shared contraction bridge from the original `SiblingLeafContract`, dispatches all possible positions of the two selected smallest weights, and returns a normalized `SiblingLeafContract` for the two selected smallest weights, in either sibling orientation, with no larger weighted external path length and a preserved leaf multiset. |
| Contracted multiset and cost-split form of normalized contraction | available-local | `InsertionScheduleTree.exists_relabelLeaves_contract_for_two_smallest_deepest_pair_anywhere_with_contracted_perm` strengthens the normalized contraction theorem with the exact weighted-cost split across the selected two-smallest contraction and the contracted leaf multiset `((a + b) :: rest.map Prod.snd)`, which are the local ingredients needed to lift the contracted-instance induction hypothesis back to the original tree. |
| Nonnegative induction-data form of normalized contraction | available-local | `InsertionScheduleTree.exists_relabelLeaves_contract_for_two_smallest_deepest_pair_anywhere_with_induction_data` further packages preservation of nonnegative contracted leaves and strict contracted leaf-count decrease relative to the original tree, supplying the induction measure and nonnegativity transfer needed by the Huffman lift. |
| Branch-specific smallest-two-at-deepest-sibling tree assembly | available-local | `InsertionScheduleTree.exists_tree_for_deepest_pair_noop_eq`, `InsertionScheduleTree.exists_tree_for_two_pair_exchange_of_two_smallest_decomposition_eq`, `InsertionScheduleTree.exists_tree_for_two_pair_exchange_reverse_of_two_smallest_decomposition_eq`, `InsertionScheduleTree.exists_tree_for_two_pair_exchange_before_deepest_of_two_smallest_decomposition_eq`, `InsertionScheduleTree.exists_tree_for_two_pair_exchange_reverse_before_deepest_of_two_smallest_decomposition_eq`, `InsertionScheduleTree.exists_tree_for_two_pair_exchange_around_deepest_of_two_smallest_decomposition_eq`, `InsertionScheduleTree.exists_tree_for_two_pair_exchange_reverse_around_deepest_of_two_smallest_decomposition_eq`, `InsertionScheduleTree.exists_tree_for_left_deepest_two_smallest_decomposition_eq`, `InsertionScheduleTree.exists_tree_for_right_deepest_two_smallest_decomposition_eq`, `InsertionScheduleTree.exists_tree_for_left_deepest_second_two_smallest_decomposition_eq`, `InsertionScheduleTree.exists_tree_for_right_deepest_second_two_smallest_decomposition_eq`, `InsertionScheduleTree.exists_tree_for_left_deepest_two_smallest_before_deepest_decomposition_eq`, `InsertionScheduleTree.exists_tree_for_right_deepest_two_smallest_before_deepest_decomposition_eq`, `InsertionScheduleTree.exists_tree_for_left_deepest_second_two_smallest_before_deepest_decomposition_eq`, `InsertionScheduleTree.exists_tree_for_right_deepest_second_two_smallest_before_deepest_decomposition_eq` |
| Combined nonoverlap occurrence-to-tree classifiers | available-local | `InsertionScheduleTree.exists_tree_for_first_before_deepest_two_smallest_nonoverlap_anywhere`, `InsertionScheduleTree.exists_tree_for_first_after_deepest_two_smallest_nonoverlap_anywhere` |
| Combined first-outside overlap/nonoverlap classifiers | available-local | `InsertionScheduleTree.exists_tree_for_first_before_deepest_two_smallest_anywhere`, `InsertionScheduleTree.exists_tree_for_first_after_deepest_two_smallest_anywhere` |
| Combined first-inside overlap/no-op classifiers | available-local | `InsertionScheduleTree.exists_tree_for_left_deepest_first_two_smallest_anywhere`, `InsertionScheduleTree.exists_tree_for_right_deepest_first_two_smallest_anywhere` |
| Arbitrary smallest-two/deepest-sibling branch classification | available-local | `InsertionScheduleTree.exists_tree_for_two_smallest_deepest_pair_anywhere` combines the selected-relative-to-adjacent-pair split with the first-before, first-after, left-deepest-first, and right-deepest-first classifiers. |
| Contraction-ready smallest/deepest sibling witness | available-local | `InsertionScheduleTree.exists_tree_for_two_smallest_deepest_pair_anywhere_pair_witness` strengthens the arbitrary classifier by returning explicit adjacent deepest-pair placement for the two selected smallest weights, in either sibling orientation. |
| Tree-level two-smallest deepest-pair placement | available-local | `InsertionScheduleTree.exists_tree_with_two_smallest_at_deepest_pair` combines deepest sibling existence, two-smallest decomposition, depth bounds, and the pair witness to normalize any nontrivial schedule. |
| Structural sibling-leaf contraction relation | available-local | `InsertionScheduleTree.SiblingLeafContract`, `InsertionScheduleTree.SiblingLeafContract.exactEval_eq`, `InsertionScheduleTree.SiblingLeafContract.leafCount_eq_succ`, `InsertionScheduleTree.SiblingLeafContract.contracted_leafCount_lt`, `InsertionScheduleTree.SiblingLeafContract.exists_leaves_context`, `InsertionScheduleTree.SiblingLeafContract.exists_leafDepthWeights_context`, `InsertionScheduleTree.SiblingLeafContract.exists_leafDepthWeights_and_leaves_context`, `InsertionScheduleTree.SiblingLeafContract.exists_leafDepthWeights_context_with_relabel_contract`, `InsertionScheduleTree.SiblingLeafContract.exists_expansion_of_mem`, `InsertionScheduleTree.SiblingLeafContract.contracted_leaves_nonnegative`, and `InsertionScheduleTree.SiblingLeafContract.weightedLeafDepthCost_eq` provide the tree-level contraction API, induction measure, hypothesis transfer, explicit depth-list contraction display, matching plain leaf contexts, branch-ready same-shape relabeling contraction, inverse merged-leaf expansion, and cost/leaf facts. |
| Same-shape relabeling preserves sibling contraction | available-local | `InsertionScheduleTree.SiblingLeafContract.relabelLeaves_contract_of_context_lengths` records the old sibling-pair context lengths and proves that arbitrary replacement weights in those slots still yield a `SiblingLeafContract` after relabeling the tree and contracted tree. |
| Sibling-contraction leaf-multiset bridges | available-local | `InsertionScheduleTree.SiblingLeafContract.leaves_perm_of_contracted_perm` expands a contracted-leaf permutation back to the original sibling leaves, and `InsertionScheduleTree.SiblingLeafContract.contracted_perm_of_leaves_perm` contracts an original-leaf permutation forward to the merged-weight instance. |
| Deepest sibling-leaf contraction existence | available-local | `InsertionScheduleTree.exists_deepest_sibling_leaf_contract` packages an actual `SiblingLeafContract` for a maximum-depth sibling pair together with the explicit deepest-pair display, weighted-cost identity, and leaf-count decrease; `InsertionScheduleTree.exists_deepest_sibling_leaf_contract_with_parent_context` rewrites that display into the `parentDepth + 1` form needed by the contraction normalizer while preserving the maximum-depth equality; `InsertionScheduleTree.exists_deepest_sibling_leaf_contract_with_relabel_parent_context` threads the same-length relabel invariant through the exact deepest context; `InsertionScheduleTree.exists_deepest_sibling_leaf_contract_with_branch_bridge` packages that context as the branch bridge consumed by the normalizer; `InsertionScheduleTree.exists_deepest_sibling_leaf_contract_with_leaf_context` additionally returns the matching plain leaf-list context. |
| Huffman contraction induction | available-local | `InsertionScheduleTree.exists_pair_decomposition_of_weights_perm_cons_cons`, `InsertionScheduleTree.exists_relabelLeaves_contract_for_two_smallest_deepest_pair_anywhere_of_context_with_contracted_perm`, `InsertionScheduleTree.exists_relabelLeaves_contract_for_two_smallest_deepest_pair_anywhere_of_context_with_induction_data`, `InsertionScheduleTree.exists_relabelLeaves_contract_for_two_smallest_deepest_pair_anywhere_with_induction_data_of_tree`, `InsertionScheduleTree.GreedyInsertionTree`, `InsertionScheduleTree.exists_greedyInsertionTree_weightedLeafDepthCost_le`, `InsertionScheduleTree.exists_greedyInsertionTree_exactMergeCost_le`, `InsertionScheduleTree.GreedyInsertionTree.weightedLeafDepthCost_le`, and `InsertionScheduleTree.GreedyInsertionTree.exactMergeCost_le` close both the existential and supplied-greedy exact nonnegative Huffman/optimal-merge theorem surfaces. |
| Exact-arithmetic Algorithm 4.1 greedy bridge | available-local | `SumTree.runningErrorBudget_exactWithUnitRoundoff_greedyInsertion_le` composes supplied-greedy exact merge-cost optimality with materialization of arbitrary `SumTree`s under `FPModel.exactWithUnitRoundoff`. |
| Concrete insertion trace realizes greedy tree | available-local | `insertionScheduleAfter_full_greedy_exactWithUnitRoundoff_of_ne_nil`, `fl_insertionSumList_has_greedy_schedule_exactWithUnitRoundoff_of_ne_nil`, and `fl_insertionSumList_exactWithUnitRoundoff_greedy_runningErrorBudget_le` prove that the source-level trace is greedy and has no larger exact-arithmetic running-error budget than any nonnegative Algorithm 4.1 tree with the same leaf multiset. |
| Literal arbitrary-`FPModel` computed-bound minimization | route-choice | Either restrict the formal p. 91 theorem to exact-arithmetic running-error objective, or add model assumptions ensuring nonnegative rounded sums and order-compatible greedy choices. |

## Frozen Work

The exact-arithmetic p. 91 insertion-optimality theorem family is closed.  Do
not add adjacent p. 91 adapters that merely restate this bridge.  Count new
progress only if the literal arbitrary-`FPModel` route choice is resolved with
a corrected theorem surface or a failed proof route is ruled out with evidence.
