import NumStability.Algorithms.PolynomialEvaluation.ElementaryErrorBounds

/-!
# Algorithms PolynomialEvaluation ElementaryErrorBounds canonical-import test

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.Horner`
during wave W12 and must resolve from the canonical path alone.
-/

#check @NumStability.fl_add_abs_error_bound
#check @NumStability.fl_mul_abs_error_bound
#check @NumStability.fl_mul_error_of_operand_error
