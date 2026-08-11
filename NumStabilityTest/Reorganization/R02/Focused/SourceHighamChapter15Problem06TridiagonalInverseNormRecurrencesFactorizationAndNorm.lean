import NumStability.Source.Higham.Chapter15.Problem06.TridiagonalInverseNorm.Recurrences.FactorizationAndNorm

/-!
# Frozen route and private-normalized closure: `NumStability.Source.Higham.Chapter15.Problem06.TridiagonalInverseNorm.Recurrences.FactorizationAndNorm`

Exercises the frozen declaration route together with the reviewed private
normalization. The private members re-mangle against this module and are
not addressable from here; the public members of the private reverse
closure that live here are checked instead, which is what pins the
normalization observably.
-/

#check @NumStability.Higham15Problem15_6.H15_Problem15_6_of_irreducible_rightInverse
#check @NumStability.Higham15Problem15_6.absInvMul_correct
#check @NumStability.Higham15Problem15_6.backward_column_scaled
#check @NumStability.Higham15Problem15_6.backward_row_scaled
#check @NumStability.Higham15Problem15_6.forward_column_scaled
#check @NumStability.Higham15Problem15_6.forward_row_scaled
#check @NumStability.Higham15Problem15_6.infNorm_correct
#check @NumStability.Higham15Problem15_6.lower_factorization
#check @NumStability.Higham15Problem15_6.p_correct
#check @NumStability.Higham15Problem15_6.qResidual_ne
#check @NumStability.Higham15Problem15_6.qResidual_scaled
#check @NumStability.Higham15Problem15_6.q_correct
#check @NumStability.Higham15Problem15_6.upper_factorization
#check @NumStability.Higham15Problem15_6.x_correct
#check @NumStability.Higham15Problem15_6.yResidual_ne
#check @NumStability.Higham15Problem15_6.yResidual_scaled
#check @NumStability.Higham15Problem15_6.y_correct
