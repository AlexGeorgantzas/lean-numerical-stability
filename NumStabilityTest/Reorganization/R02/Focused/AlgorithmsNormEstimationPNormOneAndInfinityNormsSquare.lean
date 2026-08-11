import NumStability.Algorithms.NormEstimation.PNorm.OneAndInfinityNorms.Square

/-!
# Frozen route and private-normalized closure: `NumStability.Algorithms.NormEstimation.PNorm.OneAndInfinityNorms.Square`

Exercises the frozen declaration route together with the reviewed private
normalization. The private members re-mangle against this module and are
not addressable from here; the public members of the private reverse
closure that live here are checked instead, which is what pins the
normalization observably.
-/

#check @NumStability.Ch15.exists_nonincreasing_step_of_fin_labels
#check @NumStability.Ch15.gammaSeq_one_succ_eq_column
#check @NumStability.Ch15.holder_inf
#check @NumStability.Ch15.infRowValue
#check @NumStability.Ch15.oneColumnValue
#check @NumStability.Ch15.pNormPair_inf
