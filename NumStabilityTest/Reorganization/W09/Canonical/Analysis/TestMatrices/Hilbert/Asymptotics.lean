import NumStability.Analysis.TestMatrices.Hilbert.Asymptotics

/-!
# Asymptotics canonical-only test (R_HILBERT, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28Asymptotics`
during wave W09 and must resolve from R_HILBERT alone.
-/
#check @NumStability.shiftedHilbertMatrix
#check @NumStability.HilbertDetLeadingLogRate
#check @NumStability.ShiftedHilbertNormAsymptotic
