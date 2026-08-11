import NumStability.Algorithms.NormEstimation.PNorm.OneAndInfinityNorms.Rectangular

/-!
# Frozen route and private-normalized closure: `NumStability.Algorithms.NormEstimation.PNorm.OneAndInfinityNorms.Rectangular`

Exercises the frozen declaration route together with the reviewed private
normalization. The private members re-mangle against this module and are
not addressable from here; the public members of the private reverse
closure that live here are checked instead, which is what pins the
normalization observably.
-/

#check @NumStability.RectPNormPair.holder_inf
#check @NumStability.RectPNormPair.infNormVec_rectMatVec_le
#check @NumStability.RectPNormPair.infinity
#check @NumStability.RectPNormPair.one
#check @NumStability.RectPNormPair.oneNormVec_rectMatVec_le
#check @NumStability.RectPNormPair.signVec_infNorm_eq_one
