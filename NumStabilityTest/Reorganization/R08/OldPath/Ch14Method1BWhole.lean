import NumStability.Algorithms.Ch14Method1BWhole

/-!
# Ch14Method1BWhole old-path-only test

Imports only the historical path. Every declaration checked below is part of
the residual C0004 surface that wave R08 relocated to
`NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method1B.BlockResidual.WholeMatrixBounds`,
so this compiles only if the compatibility module still re-exports it
under its original name.
-/
#check @NumStability.Ch14Ext.ch14ext_m1bInv_right_residual
#check @NumStability.Ch14Ext.ch14ext_m1b_block_right_residual
#check @NumStability.Ch14Ext.ch14ext_method1B_whole_right_residual
#check @NumStability.Ch14Ext.ch14ext_method1B_whole_right_residual_normwise
