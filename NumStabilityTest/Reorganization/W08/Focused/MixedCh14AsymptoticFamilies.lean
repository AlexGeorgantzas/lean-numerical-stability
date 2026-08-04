import NumStability.Analysis.FirstOrder.MatrixFamilies.AsymptoticFamilies
import NumStability.Source.Higham.Chapter14.Problem05.InverseBasedSolve.AsymptoticFamilies
import NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.AsymptoticFamilies
import NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method1.AsymptoticFamilies

/-!
# Ch14AsymptoticFamilies mixed-owner routing

`NumStability.Algorithms.Ch14AsymptoticFamilies` is one of the three owners B0007 requires to be split
declaration by declaration. This test imports both sides of that cut and
checks a declaration from each, so a wholesale reclassification in either
direction would fail to compile.
-/
#check @NumStability.Ch14Ext.MatrixFamilyIsBigOOne
#check @NumStability.Ch14Ext.ch14ext_problem14_5_left_familyRemainder
#check @NumStability.Ch14Ext.Ch14Eq143Family
#check @NumStability.Ch14Ext.ch14ext_eq14_6_familyX
