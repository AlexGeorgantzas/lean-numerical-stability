import NumStability.Source.Higham.Chapter14.Algorithm04.Execution.GJEOperationalBridge

/-!
# GJEOperationalBridge canonical-only test (D11, source)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.Ch14GJEOperationalBridge`
during wave W08 and must resolve from D11 alone.
-/
#check @NumStability.Ch14Ext.ch14ext_mulBiasedModel
#check @NumStability.Ch14Ext.ch14ext_gjeFinalDiagonal
#check @NumStability.Ch14Ext.ch14ext_gjeFinalizedSourceQ
