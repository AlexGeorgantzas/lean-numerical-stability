import NumStability.Analysis.Perturbation.LeastSquares.Normwise

/-!
# Normwise canonical-only import smoke test

Imports exactly one canonical module so no sibling import can supply
the declarations checked below.
-/

#check @NumStability.lsNormwiseBackwardErrorMu
#check @NumStability.lsNormwiseBackwardErrorPhi
#check @NumStability.lsNormwiseBackwardErrorEtaF
