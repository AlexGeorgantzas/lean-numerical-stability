import NumStability.Algorithms.LinearSystems.GaussJordan.ErrorAnalysis.GaussJordan
import NumStability.Algorithms.MatrixInversion.LUFactors.ErrorAnalysis.MatrixInversion
import NumStability.Algorithms.MatrixInversion.LUFactors.Methods.MatrixInversion
import NumStability.Algorithms.MatrixInversion.Residuals.MatrixInversion
import NumStability.Algorithms.MatrixInversion.Triangular.ErrorAnalysis.MatrixInversion
import NumStability.Algorithms.MatrixInversion.Triangular.Specifications.MatrixInversion
import NumStability.Analysis.Error.MatrixProducts.Contracts.MatrixInversion
import NumStability.Analysis.Error.MatrixProducts.EvaluationTrees.ProductErrorNotation
import NumStability.Analysis.FirstOrder.MatrixFamilies.AsymptoticFamilies

/-!
# Reusable inversion and Gauss-Jordan API surface

Imports every reusable W08 destination (D01-D09) and nothing else. No Source
module and no historical facade appears in this import list, so the reusable
tier is shown to be usable on its own terms.
-/
#check @NumStability.gje_c₃
#check @NumStability.methodA_forward_error
#check @NumStability.methodAComputedInverse
#check @NumStability.ideal_forward_error
#check @NumStability.triInv_method1_forward_error
#check @NumStability.Method2Spec
#check @NumStability.MatProdError
#check @NumStability.Ch14ProductTree
#check @NumStability.Ch14Ext.MatrixFamilyIsBigOOne
