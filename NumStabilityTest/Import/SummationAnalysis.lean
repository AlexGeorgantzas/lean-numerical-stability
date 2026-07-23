import NumStability.Analysis.Summation

/-!
# Summation-analysis aggregate smoke test

The family umbrella must expose both the reusable sign API and the mixed
floating-point error layer.
-/

#check NumStability.OneSigned
#check NumStability.fl_sum_error
