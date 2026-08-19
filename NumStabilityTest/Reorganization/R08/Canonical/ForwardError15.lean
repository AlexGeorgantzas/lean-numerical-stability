import NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.ScaledPerturbationEndpoints.ForwardError

/-!
# ForwardError canonical-only test

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.Ch14ForwardErrorEndpoint`
during wave R08 and must resolve from this destination alone.
-/
#check @NumStability.Ch14Ext.ch14ext_eq14_3_quadraticRemainder_isBigO
#check @NumStability.Ch14Ext.ch14ext_eq14_6_method1_forward_error_endpoint
#check @NumStability.Ch14Ext.ch14ext_eq14_6_method1_quadraticRemainder_isBigO
#check @NumStability.Ch14Ext.ch14ext_problem14_5_left_inverse_solve_forward_error_endpoint
#check @NumStability.Ch14Ext.ch14ext_problem14_5_left_quadraticRemainder_isBigO
#check @NumStability.Ch14Ext.ch14ext_problem14_5_right_inverse_solve_forward_error_endpoint
#check @NumStability.Ch14Ext.ch14ext_problem14_5_right_quadraticRemainder_isBigO
