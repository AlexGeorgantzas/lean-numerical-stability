import NumStability.Source.Higham.Chapter14.Section03.LUFactorInversion.MethodB.MethodsBC

/-!
# MethodsBC canonical-only test (D39, source)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.Ch14MethodsBC`
during wave W08 and must resolve from D39 alone.
-/
#check @NumStability.Ch14Ext.ch14ext_methodB_eq14_18
#check @NumStability.Ch14Ext.ch14ext_methodBUpperInverse
#check @NumStability.Ch14Ext.ch14ext_LUBackwardError_mono
