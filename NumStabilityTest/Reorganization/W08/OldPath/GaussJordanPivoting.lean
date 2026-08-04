import NumStability.Algorithms.GaussJordanPivoting

/-!
# GaussJordanPivoting old-path-only test

Imports only the historical path. Every declaration checked below moved to a
canonical module during wave W08, so this compiles only if the compatibility
module still re-exports it under its original name.
-/
#check @NumStability.Ch14Ext.Ch14GJEState
#check @NumStability.Ch14Ext.ch14ext_swap
#check @NumStability.Ch14Ext.ch14ext_reduce
