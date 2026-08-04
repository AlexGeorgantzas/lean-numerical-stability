import NumStability.Source.Higham.Chapter14.Corollary07.DiagonalDominance.Basic

/-!
# Basic canonical-only test (D15, source)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.Ch14Corollary147`
during wave W08 and must resolve from D15 alone.
-/
#check @NumStability.Ch14Ext.ch14ext_cor147_absLU_rowSum_le
#check @NumStability.Ch14Ext.ch14ext_cor147_absLU_infNorm_le
#check @NumStability.Ch14Ext.ch14ext_cor147_condU_infNorm_le
