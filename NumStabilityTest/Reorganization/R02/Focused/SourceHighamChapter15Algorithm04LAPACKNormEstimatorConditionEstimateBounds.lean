import NumStability.Source.Higham.Chapter15.Algorithm04.LAPACKNormEstimator.ConditionEstimate.Bounds

/-!
# Frozen route and private-normalized closure: `NumStability.Source.Higham.Chapter15.Algorithm04.LAPACKNormEstimator.ConditionEstimate.Bounds`

Exercises the frozen declaration route together with the reviewed private
normalization. The private members re-mangle against this module and are
not addressable from here; the public members of the private reverse
closure that live here are checked instead, which is what pins the
normalization observably.
-/

#check @NumStability.Higham15.H15_Algorithm15_4_condEstimate_le_kappaOne
#check @NumStability.Higham15.H15_Algorithm15_4_exact_ratio_witness
#check @NumStability.Higham15.H15_Algorithm15_4_lower_bound
#check @NumStability.Higham15.H15_Algorithm15_4_ratio_witness
#check @NumStability.Higham15.H15_Algorithm15_4_scaled_le_kappaOne
