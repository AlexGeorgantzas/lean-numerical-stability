import NumStability.Algorithms.Ch14AsymptoticFamilies

/-!
# Ch14AsymptoticFamilies old-path-only test

Imports only the historical path. Every declaration checked below is part of
the residual C0004 surface that wave R08 relocated to
`NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.ComposedCoefficientFamilies.RemainderAsymptotics`,
so this compiles only if the compatibility module still re-exports it
under its original name.
-/
#check @NumStability.Ch14Ext.ch14ext_eq14_6_familyRemainder_isBigO
#check @NumStability.Ch14Ext.ch14ext_eq14_6_vanishing_family_endpoint
#check @NumStability.Ch14Ext.ch14ext_eq14_7_familyRemainder_isBigO
#check @NumStability.Ch14Ext.ch14ext_eq14_7_vanishing_family_endpoint
#check @NumStability.Ch14Ext.ch14ext_problem14_5_left_familyRemainder_isBigO
#check @NumStability.Ch14Ext.ch14ext_problem14_5_left_vanishing_family_endpoint
#check @NumStability.Ch14Ext.ch14ext_problem14_5_right_familyRemainder_isBigO
#check @NumStability.Ch14Ext.ch14ext_problem14_5_right_vanishing_family_endpoint
