import NumStability.Analysis.MatrixConcentration

/-!
# R10 ProtectedCanonicalTargets test

Canonical forward targets of this wave's compatibility wrappers that no
other test module imports directly. The compatibility contract requires a
direct test import for every canonical target, so this module supplies it.
-/

#check @NumStability.real_exp_neg_log_two_mul_div_mul_self_add
