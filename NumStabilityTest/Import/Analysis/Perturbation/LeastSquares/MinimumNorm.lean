import NumStability.Analysis.Perturbation.LeastSquares.MinimumNorm

/-!
# MinimumNorm canonical-only import smoke test

Imports exactly one canonical module so no sibling import can supply
the declarations checked below.
-/

#check @NumStability.lsMinimumNormBackwardErrorEtaF
#check @NumStability.lsMinimumNormBackwardErrorValuesF
#check @NumStability.IsMinimumNormLeastSquaresMinimizer
