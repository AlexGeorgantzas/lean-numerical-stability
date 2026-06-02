import LeanFpAnalysis.HDP

open LeanFpAnalysis.HDP

/-!
Executable lookup file for the HDP side of the library.

Run:

  lake env lean examples/HDPLibraryLookup.lean
-/

-- Convex geometry core
#check PairwiseNormBound
#check empiricalAverage
#check diam_le_of_pairwiseNormBound
#check pairwiseNormBound_of_diam_le
#check convex_combo_dist_le_pairwise
#check maurey_sum_deviation_sq
#check norm_sum_deviation_le

-- Appetizer theorems
#check caratheodory_finiteDimensional
#check approximate_caratheodory
#check approximate_caratheodory_unit
#check approximate_caratheodory_theorem_0_0_2
#check approximate_caratheodory_of_diam_le

-- Covering polytopes by balls
#check empiricalCenters
#check empiricalCenters_ncard_le
#check convexHull_covered_by_empiricalCenters
#check covering_polytopes_by_balls_param
#check convexHull_subset_iUnion_closedBall_empiricalCenters
#check one_div_sqrt_natCeil_one_div_sq_le
#check covering_polytopes_by_balls
#check covering_polytope_by_balls_named
#check unorderedEmpiricalCenters
#check unorderedEmpiricalCenters_ncard_le_choose
#check improved_covering_polytopes_by_balls_param
#check improved_covering_polytopes_by_balls
#check improved_covering_polytopes_by_balls_exists_C

-- Binomial bounds from Exercise 0.0.5
#check choose_lower_bound
#check choose_le_sum_range_choose
#check sum_range_choose_le_exp_mul_div
#check exercise_0_0_5_binomial_chain

-- Variance identities from Exercise 0.0.3
#check productWeight
#check productWeight_snoc
#check sum_productWeight
#check norm_sum_sq_of_pairwise_inner_zero
#check weighted_variance_sum_independent
#check weighted_variance_identity

-- Chapter 1, Section 1.1: random-variable notation and identities
#check expectation
#check expectation_def
#check momentGeneratingFunction
#check momentGeneratingFunction_eq_mgf
#check rawMoment
#check absoluteMoment
#check eAbsoluteMoment
#check lpNorm
#check l2Inner
#check l2Norm
#check l2Norm_eq_sqrt_absMoment
#check standardDeviation
#check variance_eq_expectation_sq_sub_mean
#check standardDeviation_sq
#check standardDeviation_eq_l2Norm_centered
#check covariance_eq_l2Inner_centered
#check centralMoment_two_eq_variance
#check distribution
#check cumulativeDistribution
#check upperTail
#check lowerTail
#check cumulativeDistribution_eq_distribution_Iic
#check upperTail_eq_one_sub_cdf
#check standardNormalDensity
#check standardNormalDensity_eq

-- Chapter 1, Section 1.2: inequalities and tail identities
#check jensen_integral
#check lpNorm_mono_exponent
#check minkowski_eLpNorm
#check holder_integral_mul_abs
#check cauchy_schwarz_integral_mul
#check integral_identity_nonnegative
#check integral_identity_real
#check eAbsoluteMoment_eq_lintegral_tail
#check markov_inequality
#check chebyshev_inequality

-- Chapter 1, Section 1.3: limit-theorem infrastructure
#check lawOf
#check partialSum
#check sampleMean
#check variance_sampleMean_eq
#check strong_law_large_numbers_real
#check standardNormalProbability
#check standardNormal_tail_eq_integral
#check normalizedSum
#check centralLimitConclusion
#check LindebergLevyCLTHypotheses
#check lindebergLevyCentralLimitTheoremStatement
#check bernoulliNatPMF
#check binomialNatPMF
#check poissonPointProbability
#check poissonPointProbability_eq
#check poissonProbabilityMeasure
#check poissonTriangularSum
#check rowParameterSum
#check rowParameterMax
#check poissonLimitConclusion
#check PoissonLimitTheoremHypotheses
#check poissonLimitTheoremStatement
#check probabilityMeasure_nat_tendsto_of_singleton
#check poisson_limit_of_point_probabilities
