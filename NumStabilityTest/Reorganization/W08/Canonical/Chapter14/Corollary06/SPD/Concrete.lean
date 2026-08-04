import NumStability.Source.Higham.Chapter14.Corollary06.SPD.Concrete

/-!
# Concrete canonical-only test (D14, source)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.Ch14Corollary146Concrete`
during wave W08 and must resolve from D14 alone.
-/
#check @NumStability.Ch14Ext.ch14ext_cor146_absLU_budget
#check @NumStability.Ch14Ext.ch14ext_cor146_luDelta_opNorm2Le
#check @NumStability.Ch14Ext.ch14ext_cor146_absLU_eq_absRT_absR
