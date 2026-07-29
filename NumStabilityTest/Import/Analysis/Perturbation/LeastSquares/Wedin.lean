import NumStability.Analysis.Perturbation.LeastSquares.Wedin

/-!
# Wedin canonical-only import smoke test

Imports exactly one canonical module so no sibling import can supply
the declarations checked below.
-/

#check @NumStability.WedinPerturbationBound
#check @NumStability.wedinLemma20_11_sigmaMinCol
#check @NumStability.wedinLemma20_11_denominator_pos
