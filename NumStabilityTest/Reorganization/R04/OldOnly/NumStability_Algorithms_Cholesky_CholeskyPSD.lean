import NumStability.Algorithms.Cholesky.CholeskyPSD

/-!
# CholeskyPSD old-path-only test (R04)

Imports only the historical path. Every declaration checked below moved to
a canonical destination during wave R04, so this compiles only if the
compatibility surface still re-exports it under its original name.
-/
#check @NumStability.fl_cpFactor_rows_dominated
#check @NumStability.fl_cp_termination_trailing_bound
#check @NumStability.fl_factor_row_dominated
#check @NumStability.higham10_14_as_run_backward_error
#check @NumStability.psd_abs_entry_le_maxdiag
#check @NumStability.psd_abs_entry_le_sqrt_diag
#check @NumStability.psd_all_diag_zero
#check @NumStability.psd_cholesky_existence
#check @NumStability.psd_pivoted_cholesky_exists
#check @NumStability.psd_pivoted_cholesky_exists_cp
#check @NumStability.psd_pivoted_cholesky_exists_tail
#check @NumStability.psd_quadForm_le_card_maxdiag
#check @NumStability.psd_quadForm_le_trace
#check @NumStability.spd_pivoted_cholesky
