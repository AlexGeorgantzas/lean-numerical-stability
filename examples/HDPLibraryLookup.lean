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
#check convex_combo_dist_le_pairwise
#check maurey_sum_deviation_sq
#check norm_sum_deviation_le

-- Appetizer theorems
#check caratheodory_finiteDimensional
#check approximate_caratheodory
#check approximate_caratheodory_unit
#check approximate_caratheodory_theorem_0_0_2

-- Covering polytopes by balls
#check empiricalCenters
#check empiricalCenters_ncard_le
#check convexHull_covered_by_empiricalCenters
#check covering_polytopes_by_balls_param
#check one_div_sqrt_natCeil_one_div_sq_le
#check covering_polytopes_by_balls
#check unorderedEmpiricalCenters
#check unorderedEmpiricalCenters_ncard_le_choose
#check improved_covering_polytopes_by_balls_param
#check improved_covering_polytopes_by_balls

-- Binomial bounds from Exercise 0.0.5
#check choose_lower_bound
#check choose_le_sum_range_choose
#check sum_range_choose_le_exp_mul_div
#check exercise_0_0_5_binomial_chain

-- Variance identities from Exercise 0.0.3
#check norm_sum_sq_of_pairwise_inner_zero
#check weighted_variance_identity
