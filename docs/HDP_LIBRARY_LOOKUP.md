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
| Convex combinations and empirical averages | `LeanFpAnalysis/HDP/Geometry/Convex.lean` | `PairwiseNormBound`, `empiricalAverage` | Reusable geometry core. |
| Theorem 0.0.1, Caratheodory | `LeanFpAnalysis/HDP/Appetizer/Caratheodory.lean` | `caratheodory_finiteDimensional` | Uses mathlib's `convexHull_eq_union`; bound is `finrank + 1`. |
| Theorem 0.0.2, Approximate Caratheodory | `LeanFpAnalysis/HDP/Geometry/Convex.lean`, `Appetizer/Caratheodory.lean` | `approximate_caratheodory`, `approximate_caratheodory_unit`, `approximate_caratheodory_theorem_0_0_2` | Bound is exactly `D / sqrt k`, and `1 / sqrt k` when `D = 1`. |
| Empirical-method proof infrastructure | `LeanFpAnalysis/HDP/Geometry/Convex.lean` | `maurey_sum_deviation_sq`, `norm_sum_deviation_le`, `convex_combo_dist_le_pairwise` | Deterministic Maurey-style proof; no probabilistic API dependency. |
| Exercise 0.0.3 variance identities | `LeanFpAnalysis/HDP/Probability/Variance.lean` | `norm_sum_sq_of_pairwise_inner_zero`, `weighted_variance_identity` | Algebraic finite forms of the variance identities used in the proof. |
| Corollary 0.0.4 covering polytopes | `LeanFpAnalysis/HDP/Appetizer/Covering.lean` | `empiricalCenters`, `empiricalCenters_ncard_le`, `convexHull_covered_by_empiricalCenters`, `covering_polytopes_by_balls_param`, `covering_polytopes_by_balls` | Cardinality bound is `V.card ^ ceil(1 / ε^2)`. |
| Exercise 0.0.5 binomial bounds | `LeanFpAnalysis/HDP/Combinatorics/Binomial.lean` | `choose_lower_bound`, `choose_le_sum_range_choose`, `sum_range_choose_le_exp_mul_div`, `exercise_0_0_5_binomial_chain` | Formalizes `(n/m)^m ≤ choose n m ≤ sum_{k≤m} choose n k ≤ (e n/m)^m`. |
| Exercise 0.0.6 improved covering | `LeanFpAnalysis/HDP/Appetizer/Covering.lean` | `unorderedEmpiricalCenters`, `unorderedEmpiricalCenters_ncard_le_choose`, `improved_covering_polytopes_by_balls_param`, `improved_covering_polytopes_by_balls` | Uses unordered empirical centers and gives explicit constant `C = e`. |

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
rg "variance|inner_zero|weighted_variance" LeanFpAnalysis/HDP
```
