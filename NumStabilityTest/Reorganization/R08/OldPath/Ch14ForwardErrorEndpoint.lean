import NumStability.Algorithms.Ch14ForwardErrorEndpoint

/-!
# Ch14ForwardErrorEndpoint old-path-only test

Imports only the historical path. Every declaration checked below is part of
the residual C0004 surface that wave R08 relocated to
`NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.ScaledPerturbationEndpoints.ForwardError`,
so this compiles only if the compatibility module still re-exports it
under its original name.
-/
#check @NumStability.Ch14Ext.ch14ext_eq14_3_quadraticRemainder_isBigO
#check @NumStability.Ch14Ext.ch14ext_eq14_6_method1_forward_error_endpoint
#check @NumStability.Ch14Ext.ch14ext_eq14_6_method1_quadraticRemainder_isBigO
#check @NumStability.Ch14Ext.ch14ext_problem14_5_left_inverse_solve_forward_error_endpoint
#check @NumStability.Ch14Ext.ch14ext_problem14_5_left_quadraticRemainder_isBigO
#check @NumStability.Ch14Ext.ch14ext_problem14_5_right_inverse_solve_forward_error_endpoint
#check @NumStability.Ch14Ext.ch14ext_problem14_5_right_quadraticRemainder_isBigO
