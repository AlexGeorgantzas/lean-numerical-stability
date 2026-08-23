import NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.SpijkerKreiss

/-!
# R07 consumer test

imports only NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.SpijkerKreiss and checks its exact 2-declaration direct format-2 use frontier after NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.KreissBridge->NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.ArcLengthPowerBounds.FiniteDimension
-/

#check @NumStability.SpijkerArcLengthBound
#check @NumStability.norm_pow_le_exp_mul_dim_of_spijker
