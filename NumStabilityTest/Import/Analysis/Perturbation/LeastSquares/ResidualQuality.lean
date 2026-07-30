import NumStability.Analysis.Perturbation.LeastSquares.ResidualQuality

/-!
# ResidualQuality canonical-only import smoke test

Imports exactly one canonical module so no sibling import can supply
the declarations checked below.
-/

#check @NumStability.higham20QRRhsNormMajorant
#check @NumStability.higham20ConventionalResidual
#check @NumStability.higham20QRColumnNormMajorant
