import NumStability.Algorithms.Ch14GJEOperationalBridge

/-!
# Ch14GJEOperationalBridge old-path-only test

Imports only the historical path. Every declaration checked below moved to a
canonical module during wave W08, so this compiles only if the compatibility
module still re-exports it under its original name.
-/
#check @NumStability.Ch14Ext.ch14ext_mulBiasedModel
#check @NumStability.Ch14Ext.ch14ext_gjeFinalDiagonal
#check @NumStability.Ch14Ext.ch14ext_gjeFinalizedSourceQ
