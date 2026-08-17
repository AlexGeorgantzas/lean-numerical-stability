import NumStability.Algorithms.Ch14GJEAsymptoticFamilies

/-!
# Ch14GJEAsymptoticFamilies old-path-only test

Imports only the historical path. Every declaration checked below is part of
the residual C0004 surface that wave R08 relocated to
`NumStability.Source.Higham.Chapter14.Theorem05.EliminationFamilies.CoefficientAsymptotics`,
so this compiles only if the compatibility module still re-exports it
under its original name.
-/
#check @NumStability.Ch14Ext.ch14ext_gammaRem_family_isBigO_unit_sq
#check @NumStability.Ch14Ext.ch14ext_gamma_family_isBigO_unit
#check @NumStability.Ch14Ext.ch14ext_gjeConcrete_forward_14_32_vanishing_family_endpoint
#check @NumStability.Ch14Ext.ch14ext_gjeConcrete_residual_14_31_vanishing_family_endpoint
#check @NumStability.Ch14Ext.ch14ext_gjeForwardLiteralHigherOrder_family_isBigO
#check @NumStability.Ch14Ext.ch14ext_gjeResidualHigherOrder_family_isBigO
#check @NumStability.Ch14Ext.ch14ext_gje_c3_family_isBigO_unit
#check @NumStability.Ch14Ext.ch14ext_gje_c3_quadratic_remainder_family_isBigO_unit_sq
