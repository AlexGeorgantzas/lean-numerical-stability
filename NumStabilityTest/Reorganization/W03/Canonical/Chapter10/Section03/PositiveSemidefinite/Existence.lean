import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.Existence

/-!
# Chapter10 Section03 PositiveSemidefinite Existence canonical-import test

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.Cholesky.CholeskyPSD`
during wave W03 and must resolve from the canonical path alone.
-/

#check @NumStability.schur_psd
#check @NumStability.pivoted_spec_rank_R
#check @NumStability.schur_diag_le_pivot
