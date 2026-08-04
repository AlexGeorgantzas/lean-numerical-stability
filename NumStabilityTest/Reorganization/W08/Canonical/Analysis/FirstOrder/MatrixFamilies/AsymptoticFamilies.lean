import NumStability.Analysis.FirstOrder.MatrixFamilies.AsymptoticFamilies

/-!
# AsymptoticFamilies canonical-only test (D09, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.Ch14AsymptoticFamilies`
during wave W08 and must resolve from D09 alone.
-/
#check @NumStability.Ch14Ext.MatrixFamilyIsBigOOne
#check @NumStability.Ch14Ext.VectorFamilyIsBigOOne
#check @NumStability.Ch14Ext.matrixFamily_abs_isBigOOne
