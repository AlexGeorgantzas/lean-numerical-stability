import NumStability.Source.Higham.Chapter14.Problem10.EntryPerturbation.MatrixInversion

/-!
# MatrixInversion canonical-only test (D25, source)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.MatrixInversion`
during wave W08 and must resolve from D25 alone.
-/
#check @NumStability.matrixEntryPerturb
#check @NumStability.higham14_problem14_10_det_entry_perturb_eq
#check @NumStability.higham14_problem14_10_det_entry_independent_of_adjugate_eq_zero
