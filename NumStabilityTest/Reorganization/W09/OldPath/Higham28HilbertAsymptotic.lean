import NumStability.Algorithms.TestMatrices.Higham28HilbertAsymptotic

/-!
# Higham28HilbertAsymptotic old-path-only test

Imports only the historical path. Every declaration checked below moved to a
canonical module during wave W09, so this compiles only if the compatibility
module still re-exports it under its original name.
-/
#check @NumStability.log_hilbertRNat_diag_sq
#check @NumStability.centralBinomial_log_div_nat_tendsto
#check @NumStability.hilbertRNat_diag_sq_eq_centralBinomial
