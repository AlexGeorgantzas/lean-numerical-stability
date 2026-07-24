import NumStability.Algorithms.Summation.Compensated.Kahan.Coefficients

/-!
# Kahan coefficient-family smoke test

This test imports only the declaration-free coefficient aggregate and checks
one representative from each reusable engine.
-/

#check NumStability.KahanAffineCoeffStep
#check NumStability.KahanCoupledCoeffStep
