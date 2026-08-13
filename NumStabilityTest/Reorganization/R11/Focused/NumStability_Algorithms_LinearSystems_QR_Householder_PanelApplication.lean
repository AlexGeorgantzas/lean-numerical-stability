import NumStability.Algorithms.LinearSystems.QR.Householder.PanelApplication

/-!
# R11 focused test — `PanelApplication`

Exercises the frozen B0003 declaration route into `NumStability.Algorithms.LinearSystems.QR.Householder.PanelApplication`
(89 public declarations) and its private-normalized closure
(12 approved private rows).

The private check constructs each mangled `Lean.Name` explicitly, including
the numeric private component via `Name.num`, and requires the P0003
post-delivery name to be present AND the pre-delivery name to be absent.
Requiring the absence is what makes this a normalization test rather than
an existence test.

-/

private def appendNameParts (baseName : Lean.Name) (parts : List String) : Lean.Name :=
  parts.foldl (fun name part => .str name part) baseName

private def mangledPrivateName (moduleName declarationName : String)
    (ordinal : Nat) : Lean.Name :=
  let modulePrefix := appendNameParts .anonymous ("_private" :: moduleName.splitOn ".")
  appendNameParts (.num modulePrefix ordinal) (declarationName.splitOn ".")

/-- The exact P0003-approved post-delivery private names for this destination. -/
private def approvedPrivateNames : List Lean.Name := [
  mangledPrivateName "NumStability.Algorithms.LinearSystems.QR.Householder.PanelApplication" "NumStability.abs_add_three_le_householderSupport" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.QR.Householder.PanelApplication" "NumStability.abs_one_add_le_one_add_of_abs_le" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.QR.Householder.PanelApplication" "NumStability.abs_sub_le_abs_add_abs" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.QR.Householder.PanelApplication" "NumStability.fl_dotProduct_abs_le_householder_budget" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.QR.Householder.PanelApplication" "NumStability.fl_householderApplyCompact_tau_abs_le" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.QR.Householder.PanelApplication" "NumStability.fl_householderApplyCompact_z_abs_le" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.QR.Householder.PanelApplication" "NumStability.fl_householderApplyCompact_z_error_bound" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.QR.Householder.PanelApplication" "NumStability.fl_mul_abs_le" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.QR.Householder.PanelApplication" "NumStability.fl_mul_error_le" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.QR.Householder.PanelApplication" "NumStability.fl_sub_error_le_abs_add_abs" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.QR.Householder.PanelApplication" "NumStability.householderAbsDotBudget_nonneg" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.QR.Householder.PanelApplication" "NumStability.householderDot_abs_le_budget" 0
]

/-- The pre-delivery names the same rows retire; none may survive. -/
private def retiredPrivateNames : List Lean.Name := [
  mangledPrivateName "NumStability.Algorithms.LinearSystems.QR.HouseholderApplySupport" "NumStability.abs_add_three_le_householderSupport" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.QR.HouseholderApplySupport" "NumStability.abs_one_add_le_one_add_of_abs_le" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.QR.HouseholderApplySupport" "NumStability.abs_sub_le_abs_add_abs" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.QR.HouseholderApplySupport" "NumStability.fl_dotProduct_abs_le_householder_budget" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.QR.HouseholderApplySupport" "NumStability.fl_householderApplyCompact_tau_abs_le" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.QR.HouseholderApplySupport" "NumStability.fl_householderApplyCompact_z_abs_le" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.QR.HouseholderApplySupport" "NumStability.fl_householderApplyCompact_z_error_bound" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.QR.HouseholderApplySupport" "NumStability.fl_mul_abs_le" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.QR.HouseholderApplySupport" "NumStability.fl_mul_error_le" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.QR.HouseholderApplySupport" "NumStability.fl_sub_error_le_abs_add_abs" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.QR.HouseholderApplySupport" "NumStability.householderAbsDotBudget_nonneg" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.QR.HouseholderApplySupport" "NumStability.householderDot_abs_le_budget" 0
]

run_cmd do
  let environment ← Lean.getEnv
  for name in approvedPrivateNames do
    unless Lean.Environment.contains environment name do
      throwError "R11 private normalization: missing approved name {name}"
  for name in retiredPrivateNames do
    if Lean.Environment.contains environment name then
      throwError "R11 private normalization: retired name {name} still present"

#check @NumStability.coxHigham_exactSignedPivotPanelStep_active_block_bound_of_stage_bound
#check @NumStability.coxHigham_exactSignedPivotPanelStep_active_entry_bound_of_stage_bounds
#check @NumStability.coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_geometric_stage_budgets
#check @NumStability.coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound
#check @NumStability.coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_active_block_nonzero
#check @NumStability.coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_active_block_norm_pos
#check @NumStability.coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_active_max_pivot
#check @NumStability.coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_swapped_active_max_pivot
#check @NumStability.coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_swapped_active_max_pivot_of_raw_active_block_norm_pos
#check @NumStability.coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_stage_budgets
#check @NumStability.coxHigham_exactSignedPivotPanel_sequence_active_entry_bound_of_geometric_stage_budgets
#check @NumStability.coxHigham_exactSignedPivotPanel_sequence_active_entry_bound_of_stage_budgets
#check @NumStability.coxHigham_exact_same_reflector_row_growth_of_signed_pivot_row_bound
#check @NumStability.coxHigham_exact_signed_pivot_active_row_entry_bound_of_stage_bounds
#check @NumStability.coxHigham_storedPanelStep_active_entry_bound_of_exact_growth
#check @NumStability.coxHigham_storedPanelStep_active_entry_bound_of_exact_growth_factor
#check @NumStability.coxHigham_storedPanelStep_active_entry_bound_of_exact_stage_budget_factor
#check @NumStability.coxHigham_storedPanelStep_active_entry_bound_of_signed_pivot_stage_bounds
#check @NumStability.coxHigham_storedPanelStep_row_error_recurrence_of_exact_lipschitz
#check @NumStability.coxHigham_storedPanel_sequence_active_block_bound_of_signed_pivot_stage_bounds
#check @NumStability.coxHigham_storedPanel_sequence_active_entry_bound_of_exact_active_growth
#check @NumStability.coxHigham_storedPanel_sequence_active_entry_bound_of_exact_active_stage_budgets
#check @NumStability.coxHigham_storedPanel_sequence_active_entry_bound_of_exact_growth
#check @NumStability.coxHigham_storedPanel_sequence_active_entry_bound_of_exact_growth_factor
#check @NumStability.coxHigham_storedPanel_sequence_active_entry_bound_of_exact_stage_budgets_factor
#check @NumStability.coxHigham_storedPanel_sequence_rowwise_error_accumulation_bound_of_exact_lipschitz
#check @NumStability.exactSignedPivotHouseholderPanelStep
#check @NumStability.fl_householderApplyCompact
#check @NumStability.fl_householderApplyCompactPanel
#check @NumStability.fl_householderApplyCompactPanel_HouseholderColumnwisePanelAppError_of_budget
#check @NumStability.fl_householderApplyCompact_HouseholderAppError_of_budget
#check @NumStability.fl_householderApplyCompact_componentwise_error_bound
#check @NumStability.fl_householderApplyCompact_forward_error_bound
#check @NumStability.fl_householderApplyExplicit
#check @NumStability.fl_householderApplyExplicitPanel
#check @NumStability.fl_householderApplyExplicitPanel_HouseholderColumnwisePanelAppError
#check @NumStability.fl_householderApplyExplicit_HouseholderAppError
#check @NumStability.fl_householderApplyExplicit_forward_error_bound
#check @NumStability.fl_householderStoredPanelStep
#check @NumStability.fl_householderStoredPanelStep_HouseholderColumnwisePanelAppError_of_budget
#check @NumStability.fl_householderStoredPanelStep_active_entry_componentwise_error_bound
#check @NumStability.fl_householderStoredPanelStep_column_componentwise_error_bound
#check @NumStability.fl_householderStoredPanelStep_column_forward_error_bound
#check @NumStability.fl_householderStoredPanelStep_prevColumn_eq
#check @NumStability.fl_householderStoredRhsStep
#check @NumStability.fl_householderStoredRhsStep_componentwise_error_bound
#check @NumStability.fl_householderStoredRhsStep_forward_error_bound
#check @NumStability.householderAbsDotBudget
#check @NumStability.householderAbsDotBudget_le_vecNorm2_mul
#check @NumStability.householderCompactComponentBudget
#check @NumStability.householderCompactComponentBudget_eq_zero_of_vecNorm2_eq_zero
#check @NumStability.householderCompactComponentBudget_le_updateCoeff_mul_norm
#check @NumStability.householderCompactComponentBudget_nonneg
#check @NumStability.householderCompactNormBudget
#check @NumStability.householderCompactNormBudgetCoeff
#check @NumStability.householderCompactNormBudgetCoeffFactor
#check @NumStability.householderCompactNormBudgetCoeffFactor_le_fifteen_gamma
#check @NumStability.householderCompactNormBudgetCoeffFactor_le_of_u_cap_gamma_cap
#check @NumStability.householderCompactNormBudgetCoeffFactor_le_of_u_gamma_le
#check @NumStability.householderCompactNormBudgetCoeffFactor_nonneg
#check @NumStability.householderCompactNormBudgetCoeff_eq_u_add_abs_beta_norm_sq_mul_factor
#check @NumStability.householderCompactNormBudgetCoeff_le_of_abs_beta_norm_sq_le
#check @NumStability.householderCompactNormBudgetCoeff_nonneg
#check @NumStability.householderCompactNormBudget_eq_zero_of_vecNorm2_eq_zero
#check @NumStability.householderCompactNormBudget_le_mul_of_componentBudget_le_mul_abs
#check @NumStability.householderCompactNormBudget_le_normBudgetCoeff_mul
#check @NumStability.householderCompactPanelRelativeBudget
#check @NumStability.householderCompactPanelRelativeBudget_column_bound
#check @NumStability.householderCompactPanelRelativeBudget_le_mul_add_normBudgetCoeff
#check @NumStability.householderCompactPanelRelativeBudget_le_mul_add_of_column_rhs_le
#check @NumStability.householderCompactPanelRelativeBudget_le_mul_add_of_componentBudget_le_mul_abs
#check @NumStability.householderCompactPanelRelativeBudget_le_mul_add_of_normBudget_le_mul
#check @NumStability.householderCompactPanelRelativeBudget_nonneg
#check @NumStability.householderCompactPanelRelativeBudget_rhs_bound
#check @NumStability.householderCompactPanelRelativeBudget_stored_column_bound
#check @NumStability.householderCompactPanelRelativeBudget_stored_rhs_bound
#check @NumStability.householderCompactRelativeBudget
#check @NumStability.householderCompactRelativeBudget_bound
#check @NumStability.householderCompactRelativeBudget_le_normBudgetCoeff
#check @NumStability.householderCompactRelativeBudget_le_of_componentBudget_le_mul_abs
#check @NumStability.householderCompactRelativeBudget_le_of_normBudget_le_mul
#check @NumStability.householderCompactRelativeBudget_nonneg
#check @NumStability.householderCompactUpdateCoeff
#check @NumStability.householderCompactUpdateCoeff_nonneg
#check @NumStability.householderDot
#check @NumStability.matMulVec_householder_eq_compact
#check @NumStability.matMulVec_householder_signed_pivot_update_entry_eq
#check @NumStability.signedPivotHouseholderBeta
#check @NumStability.signedPivotHouseholderVector
