import NumStability.Algorithms.Ch14ForwardErrorEndpoint

/-!
# Ch14ForwardErrorEndpoint old-path-only test

Imports only the historical path. Every declaration checked below moved to a
canonical module during wave W08, so this compiles only if the compatibility
module still re-exports it under its original name.
-/
#check @NumStability.Ch14Ext.ch14ext_pull_eps_double_sum
#check @NumStability.Ch14Ext.ch14ext_gammaUnitCoefficient
#check @NumStability.Ch14Ext.ch14ext_gammaQuadraticRemainder
