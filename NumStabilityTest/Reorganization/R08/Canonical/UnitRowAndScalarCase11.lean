import NumStability.Source.Higham.Chapter14.Problem13.ConditionNumberBounds.UnitRowAndScalarCase

/-!
# UnitRowAndScalarCase canonical-only test

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Source.Higham.Chapter14.Problem13`
during wave R08 and must resolve from this destination alone.
-/
#check @NumStability.ch14ext_problem14_13_frobNorm_eq_abs_det_fin_one
#check @NumStability.ch14ext_problem14_13_gej_bound_fin_one
#check @NumStability.ch14ext_problem14_13_gej_bound_of_isRightInverse_pos
#check @NumStability.ch14ext_problem14_13_kappa2_eq_one_fin_one
#check @NumStability.ch14ext_problem14_13_kappa2_lt_two_mul_hadamardConditionNumber_of_unit_rows_pos
