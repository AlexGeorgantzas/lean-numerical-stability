import NumStability.Source.Higham.Chapter08.Lemma08Discrepancy
import NumStability.Source.Higham.Chapter10.Theorem07
import NumStability.Source.Higham.Chapter11.Theorem07
import NumStability.Source.Higham.CrossChapter.LUSolverWeights.Doolittle
import NumStability.Source.Higham.CrossChapter.LUSolverWeights.Factorization
import NumStability.Source.Higham.CrossChapter.NoGuardDotProduct
import NumStability.Source.Higham.CrossChapter.PracticalConditionBound

/-!
# Canonical source-correspondence path smoke test

Every extracted source target is imported directly, independently of the
historical forwarding paths and the aggregate Higham entry point.
-/

#check NumStability.higham8_8_printed_rowDominance_condSkeel_claim_false
#check NumStability.higham10_7_fl_cholesky_success_source
#check NumStability.Ch11Closure.TriGrowthInv.higham11_7_bunch_tridiagonal_support_aware
#check NumStability.higham12_6_lu_solve_SolverWBound
#check NumStability.higham12_6_rectRoundedLoop_lu_solve_SolverWBound_source
#check NumStability.higham15_1_eq_7_31_practical_bound_bridge
#check NumStability.higham3_5_noGuard_any_order_forward_error
