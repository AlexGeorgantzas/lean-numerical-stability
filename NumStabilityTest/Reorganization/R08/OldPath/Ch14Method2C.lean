import NumStability.Algorithms.Ch14Method2C

/-!
# Ch14Method2C old-path-only test

Imports only the historical path. Every declaration checked below is part of
the residual C0004 surface that wave R08 relocated to
`NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method2C.BlockResidual.LeftResidualBounds`,
so this compiles only if the compatibility module still re-exports it
under its original name.
-/
#check @NumStability.Ch14Ext.ch14ext_method2C_block_left_residual
