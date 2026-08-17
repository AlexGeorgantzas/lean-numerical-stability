import NumStability.Source.Higham.Chapter14.Problem13

/-!
# Problem13 aggregate completeness

`NumStability.Source.Higham.Chapter14.Problem13` is a declaration-free source aggregate after wave R08.
Importing the aggregate alone must still reach every declaration that moved
to `NumStability.Source.Higham.Chapter14.Problem13.ConditionNumberBounds.UnitRowAndScalarCase`.
-/
#check @NumStability.ch14ext_problem14_13_frobNorm_eq_abs_det_fin_one
#check @NumStability.ch14ext_problem14_13_gej_bound_fin_one
#check @NumStability.ch14ext_problem14_13_gej_bound_of_isRightInverse_pos
#check @NumStability.ch14ext_problem14_13_kappa2_eq_one_fin_one
#check @NumStability.ch14ext_problem14_13_kappa2_lt_two_mul_hadamardConditionNumber_of_unit_rows_pos
