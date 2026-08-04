import NumStability.Analysis.Error.MatrixProducts.EvaluationTrees.ProductErrorNotation

/-!
# ProductErrorNotation canonical-only test (D08, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.Ch14ProductErrorNotation`
during wave W08 and must resolve from D08 alone.
-/
#check @NumStability.Ch14ProductTree
#check @NumStability.Ch14RectProductTree
#check @NumStability.Ch14ProductTree.factors
