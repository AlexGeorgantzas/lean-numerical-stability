# LeanFpAnalysis HDP Library Lookup

This guide maps the Vershynin *High-Dimensional Probability* formalization.
The HDP library is separate from the Higham floating-point library:

```lean
import LeanFpAnalysis.HDP
open LeanFpAnalysis.HDP
```

## Appetizer Status

| Book item | Lean file | Main names | Notes |
|---|---|---|---|
| Convex combinations and empirical averages | `LeanFpAnalysis/HDP/Geometry/Convex.lean` | `PairwiseNormBound`, `empiricalAverage`, `diam_le_of_pairwiseNormBound`, `pairwiseNormBound_of_diam_le` | Reusable geometry core, with bridges to mathlib's bounded `Metric.diam` API. |
| Theorem 0.0.1, Caratheodory | `LeanFpAnalysis/HDP/Appetizer/Caratheodory.lean` | `caratheodory_finiteDimensional` | Uses mathlib's `convexHull_eq_union`; bound is `finrank + 1`. |
| Theorem 0.0.2, Approximate Caratheodory | `LeanFpAnalysis/HDP/Geometry/Convex.lean`, `Appetizer/Caratheodory.lean` | `approximate_caratheodory`, `approximate_caratheodory_unit`, `approximate_caratheodory_theorem_0_0_2`, `approximate_caratheodory_of_diam_le` | Bound is exactly `D / sqrt k`, and `1 / sqrt k` when `D = 1`; the `Metric.diam` wrapper assumes boundedness. |
| Empirical-method proof infrastructure | `LeanFpAnalysis/HDP/Geometry/Convex.lean` | `maurey_sum_deviation_sq`, `norm_sum_deviation_le`, `convex_combo_dist_le_pairwise` | Deterministic Maurey-style proof; no probabilistic API dependency. |
| Exercise 0.0.3(a), independent mean-zero sums | `LeanFpAnalysis/HDP/Probability/Variance.lean` | `productWeight`, `sum_productWeight`, `weighted_variance_sum_independent` | Finite product-distribution theorem: `E ‖sum Z_j‖^2 = sum E ‖Z_j‖^2` for iid finite weighted samples with zero mean. |
| Exercise 0.0.3(b), variance identity | `LeanFpAnalysis/HDP/Probability/Variance.lean` | `weighted_variance_identity`, `norm_sum_sq_of_pairwise_inner_zero` | Finite weighted form of `E‖Z - EZ‖² = E‖Z‖² - ‖EZ‖²`, plus the deterministic orthogonal-sum analogue. |
| Corollary 0.0.4 covering polytopes | `LeanFpAnalysis/HDP/Appetizer/Covering.lean` | `empiricalCenters`, `empiricalCenters_ncard_le`, `convexHull_covered_by_empiricalCenters`, `covering_polytopes_by_balls_param`, `covering_polytopes_by_balls`, `covering_polytope_by_balls_named`, `convexHull_subset_iUnion_closedBall_empiricalCenters` | Cardinality bound is `V.card ^ ceil(1 / ε^2)`; wrappers expose named polytopes and explicit unions of closed balls. |
| Exercise 0.0.5 binomial bounds | `LeanFpAnalysis/HDP/Combinatorics/Binomial.lean` | `choose_lower_bound`, `choose_le_sum_range_choose`, `sum_range_choose_le_exp_mul_div`, `exercise_0_0_5_binomial_chain` | Formalizes `(n/m)^m ≤ choose n m ≤ sum_{k≤m} choose n k ≤ (e n/m)^m`. |
| Exercise 0.0.6 improved covering | `LeanFpAnalysis/HDP/Appetizer/Covering.lean` | `unorderedEmpiricalCenters`, `unorderedEmpiricalCenters_ncard_le_choose`, `improved_covering_polytopes_by_balls_param`, `improved_covering_polytopes_by_balls`, `improved_covering_polytopes_by_balls_exists_C` | Uses unordered empirical centers; the strongest theorem gives explicit `C = e`, and the wrapper gives the book-style existential constant. |

## Appetizer Formalization Plan

| Phase | Scope | Status | Core files |
|---|---|---|---|
| 1 | Convex and metric infrastructure: convex combinations, empirical averages, pairwise diameter, and `Metric.diam` bridges. | Done | `Geometry/Convex.lean` |
| 2 | Caratheodory statements: exact finite-dimensional theorem and approximate theorem in both internal and book-style diameter forms. | Done | `Appetizer/Caratheodory.lean` |
| 3 | Finite probability identities: product weights, independent mean-zero variance identity, and weighted variance identity. | Done | `Probability/Variance.lean` |
| 4 | Covering corollary: ordered empirical centers, pointwise cover, explicit closed-ball union, and named-polytope wrapper with `N` vertices. | Done | `Appetizer/Covering.lean` |
| 5 | Counting estimates: binomial bounds and stars-and-bars count for unordered empirical centers. | Done | `Combinatorics/Binomial.lean`, `Appetizer/Covering.lean` |
| 6 | Improved covering exercise: concrete constant `e` and existential absolute-constant wrapper. | Done | `Appetizer/Covering.lean` |
| 7 | Library health: lookup docs, executable lookup files, and unfinished-proof/build checks. | Maintained | `docs/HDP_LIBRARY_LOOKUP.md`, `examples/HDPLibraryLookup.lean` |

## Main Dependency Chain

```text
Combinatorics.Binomial
  -> Appetizer.Covering

Geometry.Convex
  -> Appetizer.Caratheodory
  -> Appetizer.Covering

Probability.Variance is independent support material for Exercise 0.0.3.
```

## Common Imports

Use the full appetizer:

```lean
import LeanFpAnalysis.HDP.Appetizer
```

Use only the reusable convex geometry:

```lean
import LeanFpAnalysis.HDP.Geometry.Convex
```

## Search Recipes

```bash
rg "approximate_caratheodory|PairwiseNormBound|empiricalCenters" LeanFpAnalysis/HDP
rg "binomial_chain|unorderedEmpiricalCenters|improved_covering" LeanFpAnalysis/HDP
rg "variance|productWeight|weighted_variance" LeanFpAnalysis/HDP
```
