import NumStability.Analysis.Perturbation.LeastSquares.Basic

/-!
# Basic canonical-only import smoke test

Imports exactly one canonical module so no sibling import can supply
the declarations checked below.
-/

#check @NumStability.ls_qr_forward_error
#check @NumStability.qrStageHorizonBudget
#check @NumStability.qrSolveFinalRhsBudget
