import NumStability.Algorithms.Ch14Method2Loop

/-!
# Ch14Method2Loop old-path-only test

Imports only the historical path. Every declaration checked below moved to a
canonical module during wave W08, so this compiles only if the compatibility
module still re-exports it under its original name.
-/
#check @NumStability.Ch14Ext.ch14ext_method2Inv
#check @NumStability.Ch14Ext.ch14ext_method2Inv_below
#check @NumStability.Ch14Ext.ch14ext_method2Inv_store
