import NumStability.Algorithms.LinearSystems.LeastSquares.Equality.KKT

/-!
# KKT systems for equality-constrained least squares canonical-only import smoke test

Imports exactly one canonical module and checks representative public declarations.
-/

#check @NumStability.LSEKKTSystem
#check @NumStability.IsLSEMinimizer.exists_lagrange_kkt_difference_source_system_of_fullRowRank
#check @NumStability.Theorem20_10.orthogonal_matMulVec_injective
