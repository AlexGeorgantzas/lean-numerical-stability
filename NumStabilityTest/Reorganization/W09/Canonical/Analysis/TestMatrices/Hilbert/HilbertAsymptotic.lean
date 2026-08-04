import NumStability.Analysis.TestMatrices.Hilbert.HilbertAsymptotic

/-!
# HilbertAsymptotic canonical-only test (R_HILBERT, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28HilbertAsymptotic`
during wave W09 and must resolve from R_HILBERT alone.
-/
#check @NumStability.log_hilbertRNat_diag_sq
#check @NumStability.centralBinomial_log_div_nat_tendsto
#check @NumStability.hilbertRNat_diag_sq_eq_centralBinomial
