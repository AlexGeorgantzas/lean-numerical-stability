import NumStability.Source.Higham.Chapter28.Equation03.HilbertCholeskyFactor.Exact

/-!
# Exact canonical-only test (S_EQ03, source)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28Exact`
during wave W09 and must resolve from S_EQ03 alone.
-/
#check @NumStability.hilbertCholeskyFactor_det
#check @NumStability.hilbertMatrix_eq_choleskyGram
#check @NumStability.hilbert_choleskyGram_apply_of_le
