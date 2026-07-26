import NumStability.Analysis.Norms

/-!
# Historical norms facade import smoke test

This is deliberately an old-only import. It verifies that the historical path
continues to expose representatives from both the transitional extracted
core and the source-owned Higham Theorem 6.4 tail.
-/

#check NumStability.complexVecLpNorm
#check NumStability.complexMatrixLpNorm
#check NumStability.mixedInverseAmbientRelativeAmplificationRadiusSup
#check NumStability.mixedInverseAmbientRelativeAmplificationRadiusSup_tendsto_conditionNumberProduct_of_positive_radii
