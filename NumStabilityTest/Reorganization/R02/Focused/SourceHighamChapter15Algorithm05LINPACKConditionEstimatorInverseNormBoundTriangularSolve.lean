import NumStability.Source.Higham.Chapter15.Algorithm05.LINPACKConditionEstimator.InverseNormBound.TriangularSolve

/-!
# Frozen route and private-normalized closure: `NumStability.Source.Higham.Chapter15.Algorithm05.LINPACKConditionEstimator.InverseNormBound.TriangularSolve`

Exercises the frozen declaration route together with the reviewed private
normalization. The private members re-mangle against this module and are
not addressable from here; the public members of the private reverse
closure that live here are checked instead, which is what pins the
normalization observably.
-/

#check @NumStability.Ch15.linpackD_isPlusMinusOne
#check @NumStability.Ch15.linpackY_infNorm_le_infNorm_inv
#check @NumStability.Ch15.linpackY_infNorm_le_infNorm_inv_nonsingular
