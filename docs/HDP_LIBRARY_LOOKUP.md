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

## Chapter 1 Status

Chapter import:

```lean
import LeanFpAnalysis.HDP.Chapter01
```

| Book item | Lean file | Main names | Notes |
|---|---|---|---|
| Section 1.1, expectation and transforms | `LeanFpAnalysis/HDP/Probability/RandomVariables.lean` | `expectation`, `momentGeneratingFunction`, `momentGeneratingFunction_eq_mgf` | Book notation wrappers over mathlib's Bochner expectation and `mgf`. |
| Section 1.1, moments and `L^p` quantities | `Probability/RandomVariables.lean` | `rawMoment`, `absoluteMoment`, `eAbsoluteMoment`, `lpNorm`, `l2Norm`, `l2Norm_eq_sqrt_absMoment` | Includes finite-real and extended nonnegative moment forms. |
| Section 1.1, variance, standard deviation, covariance | `Probability/RandomVariables.lean` | `standardDeviation`, `variance_eq_expectation_sq_sub_mean`, `standardDeviation_sq`, `standardDeviation_eq_l2Norm_centered`, `covariance_eq_l2Inner_centered`, `centralMoment_two_eq_variance` | Uses mathlib's `Var`, `stdDev`, and covariance API; identities keep the book's normalization. |
| Section 1.1, distribution functions and normal density | `Probability/RandomVariables.lean` | `distribution`, `cumulativeDistribution`, `upperTail`, `lowerTail`, `upperTail_eq_one_sub_cdf`, `standardNormalDensity`, `standardNormalMeasure` | CDF/tail definitions and the standard normal density `exp (-x^2/2) / sqrt (2*pi)`. |
| Section 1.2, Jensen and `L^p` inequalities | `Probability/Inequalities.lean` | `jensen_integral`, `lpNorm_mono_exponent`, `minkowski_eLpNorm`, `holder_integral_mul_abs`, `cauchy_schwarz_integral_mul` | Reuses mathlib convex-integral, eLpNorm, Holder, and Cauchy-Schwarz statements. |
| Lemma 1.2.1 and Exercises 1.2.2-1.2.3 | `Probability/Inequalities.lean` | `integral_identity_nonnegative`, `integral_identity_real`, `eAbsoluteMoment_eq_lintegral_tail` | Exact layer-cake identities, including the two-sided real tail identity and extended moment-tail identity. |
| Proposition 1.2.4 and Corollary 1.2.5 | `Probability/Inequalities.lean` | `markov_inequality`, `chebyshev_inequality` | Exact book bounds: `P{X ≥ t} ≤ E X / t` and `P{|X - E X| ≥ t} ≤ Var(X)/t^2`. |
| Section 1.3, sample means and strong law | `Probability/LimitTheorems.lean` | `partialSum`, `sampleMean`, `variance_sampleMean_eq`, `strong_law_large_numbers_real` | Variance of the sample mean is exactly `σ2 / N`; SLLN wraps mathlib's real pairwise-independent strong law. |
| Theorem 1.3.2, central limit theorem | `Probability/LimitTheorems.lean` | `standardNormalProbability`, `standardNormal_tail_eq_integral`, `normalizedSum`, `centralLimitConclusion`, `LindebergLevyCLTHypotheses`, `lindebergLevyCentralLimitTheoremStatement` | Hypotheses and exact conclusion are recorded without a fake projection proof. A genuine proof still needs the characteristic-function Taylor expansion and Levy continuity theorem infrastructure. |
| Bernoulli, binomial, Poisson distributions | `Probability/LimitTheorems.lean` | `bernoulliNatPMF`, `binomialNatPMF`, `poissonPointProbability`, `poissonProbabilityMeasure` | PMF/measure definitions matching the chapter's distributions; Poisson point mass is `exp (-λ) * λ^k / k!`. |
| Theorem 1.3.4, Poisson limit theorem | `Probability/LimitTheorems.lean` | `poissonTriangularSum`, `rowParameterSum`, `rowParameterMax`, `poissonLimitConclusion`, `PoissonLimitTheoremHypotheses`, `poissonLimitTheoremStatement`, `probabilityMeasure_nat_tendsto_of_singleton`, `poisson_limit_of_point_probabilities` | Hypotheses and exact conclusion are recorded without a fake projection proof. The discrete weak-convergence bridge from point probabilities is genuinely proved; the Bernoulli triangular-array point-probability asymptotic remains to be formalized. |

## Chapter 1 Formalization Plan

| Phase | Scope | Status | Core files |
|---|---|---|---|
| 1 | Chapter import and modular probability subfiles. | Done | `Chapter01.lean`, `Probability.lean` |
| 2 | Section 1.1 notation and identities for expectations, moments, norms, variance/covariance, CDFs, tails, and standard normal density. | Done | `Probability/RandomVariables.lean` |
| 3 | Section 1.2 inequalities and tail identities, reusing mathlib's Jensen, `L^p`, Holder, layer-cake, Markov, and Chebyshev APIs. | Done | `Probability/Inequalities.lean` |
| 4 | Section 1.3 sample-mean variance and SLLN. | Done | `Probability/LimitTheorems.lean` |
| 5 | Section 1.3 CLT and Poisson limit theorem statements; discrete point-probability convergence bridge for Poisson laws. | Partial | `Probability/LimitTheorems.lean` |
| 6 | Library health: lookup docs, executable lookup file, import graph, and no unfinished proofs under `LeanFpAnalysis/HDP`. | Maintained | `docs/HDP_LIBRARY_LOOKUP.md`, `examples/HDPLibraryLookup.lean` |

## Main Dependency Chain

```text
Combinatorics.Binomial
  -> Appetizer.Covering

Geometry.Convex
  -> Appetizer.Caratheodory
  -> Appetizer.Covering

Probability.Variance is independent support material for Exercise 0.0.3.

Probability.RandomVariables
  -> Probability.Inequalities
  -> Probability.LimitTheorems
  -> Chapter01
```

## Common Imports

Use Chapter 1:

```lean
import LeanFpAnalysis.HDP.Chapter01
```

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
rg "expectation|momentGeneratingFunction|standardDeviation|cumulativeDistribution" LeanFpAnalysis/HDP
rg "jensen_integral|markov_inequality|chebyshev_inequality|integral_identity" LeanFpAnalysis/HDP
rg "strong_law|centralLimitConclusion|poissonLimitConclusion|point_probabilities" LeanFpAnalysis/HDP
```
