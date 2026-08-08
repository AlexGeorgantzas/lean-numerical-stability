import NumStability.Analysis.TestMatrices.Hilbert.Exact

/-!
# Exact canonical-only test (R_HILBERT, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28Exact`
during wave W09 and must resolve from R_HILBERT alone.
-/
#check @NumStability.hilbert_gram_sum
#check @NumStability.hilbertRNat_diag_sq
#check @NumStability.hilbertGramTelescoper
