import NumStability.Analysis.Error.MatrixProducts.EvaluationTrees.ProductErrorNotation
import NumStability.Source.Higham.Chapter14.Section01.ProductErrorNotation.ProductErrorNotation

/-!
# Ch14ProductErrorNotation mixed-owner routing

`NumStability.Algorithms.Ch14ProductErrorNotation` is one of the three owners B0007 requires to be split
declaration by declaration. This test imports both sides of that cut and
checks a declaration from each, so a wholesale reclassification in either
direction would fail to compile.
-/
#check @NumStability.Ch14ProductTree
#check @NumStability.Ch14RectProductTree.exists_productDelta_gamma_operationBudget
