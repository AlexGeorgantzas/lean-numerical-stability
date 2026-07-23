import NumStability.Algorithms.LinearSystems.Triangular
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ComparisonBounds
import NumStability.Algorithms.LinearSystems.Triangular.DiagonalDominance
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.InverseBounds

/-!
# Canonical triangular-system import

The family umbrella must expose each reviewed reusable leaf without importing
Chapter-specific triangular-system modules.
-/

#check NumStability.fl_backSub
#check NumStability.backSub_backward_error
#check NumStability.backSub_backward_error_algorithm_8_1
#check NumStability.fl_forwardSub
#check NumStability.forwardSub_backward_error
#check NumStability.IsDiagDominantUpper
#check NumStability.backSub_forward_error_diagDom
#check NumStability.comparisonMatrix
#check NumStability.abs_inv_le_compMatrix_inv
#check NumStability.forwardSub_forward_error_comparison
#check NumStability.backSub_forward_error_mu_bound
#check NumStability.triangularSolve_backward_error
