import NumStability.Analysis.TestMatrices.Hilbert.ShiftedHilbert

/-!
# ShiftedHilbert canonical-only test (R_HILBERT, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28ShiftedHilbert`
during wave W09 and must resolve from R_HILBERT alone.
-/
#check @NumStability.arctan_le_self_of_nonneg
#check @NumStability.div_one_add_sq_le_arctan
#check @NumStability.shiftedHilbertSchurKernel
