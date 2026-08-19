import NumStability.Algorithms.Ch14Problem142

/-!
# Ch14Problem142 old-path-only test

Imports only the historical path. Every declaration checked below is part of
the residual C0004 surface that wave R08 relocated to
`NumStability.Source.Higham.Chapter14.Problem02.TriangularInversion.TwoBlockFirstOrder.Derivations`,
so this compiles only if the compatibility module still re-exports it
under its original name.
-/
#check @NumStability.Ch14Ext.Higham14Problem142Method1BDerivation.right_residual_firstOrder
#check @NumStability.Ch14Ext.Higham14Problem142Method2CDerivation.left_residual_firstOrder
#check @NumStability.Ch14Ext.higham14_problem14_2_lowerBlock_mul_sub_one
#check @NumStability.Ch14Ext.higham14_problem14_2_lowerBlock_one
#check @NumStability.Ch14Ext.higham14_problem14_2_method1B_twoBlock_right_firstOrder
#check @NumStability.Ch14Ext.higham14_problem14_2_method2C_twoBlock_left_firstOrder
