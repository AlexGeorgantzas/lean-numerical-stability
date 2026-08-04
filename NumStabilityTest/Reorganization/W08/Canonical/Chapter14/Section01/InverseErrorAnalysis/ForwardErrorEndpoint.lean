import NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.ForwardErrorEndpoint

/-!
# ForwardErrorEndpoint canonical-only test (D31, source)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.Ch14ForwardErrorEndpoint`
during wave W08 and must resolve from D31 alone.
-/
#check @NumStability.Ch14Ext.ch14ext_pull_eps_double_sum
#check @NumStability.Ch14Ext.ch14ext_gammaUnitCoefficient
#check @NumStability.Ch14Ext.ch14ext_gammaQuadraticRemainder
