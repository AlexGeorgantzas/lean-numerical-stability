import NumStability.Algorithms.Ch14Method2CWhole

/-!
# Ch14Method2CWhole old-path-only test

Imports only the historical path. Every declaration checked below is part of
the residual C0004 surface that wave R08 relocated to
`NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method2C.WholeMatrixResidual.LeftResidualBounds`,
so this compiles only if the compatibility module still re-exports it
under its original name.
-/
#check @NumStability.Ch14Ext.ch14ext_method2CInv_left_residual
#check @NumStability.Ch14Ext.ch14ext_method2C_whole_left_residual
#check @NumStability.Ch14Ext.ch14ext_method2C_whole_left_residual_normwise
