import NumStability.Source.Higham.Chapter14.Section01.ProductErrorNotation.ProductErrorNotation

/-!
# ProductErrorNotation canonical-only test (D32, source)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.Ch14ProductErrorNotation`
during wave W08 and must resolve from D32 alone.
-/
#check @NumStability.Ch14RectProductTree.exists_productDelta_gamma_operationBudget
#check @NumStability.Ch14RectProductTree.productDelta_abs_le_gamma_operationBudget
#check @NumStability.Ch14RectProductTree.roundedEval_MatProdError_gamma_operationBudget
