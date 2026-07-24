import NumStability.Algorithms.FastMatMul.Internal.LegacyBounds

/-!
# Fast-multiplication legacy bounds

This isolated import protects the unsupported declarations retained only for
historical compatibility surfaces.
-/

#check NumStability.StrassenErrorBound
#check NumStability.WinogradStrassenErrorBound
#check NumStability.conventional_componentwise_implies_cubic
#check NumStability.WinogradInnerProductError
#check NumStability.BilinearAlgorithmError
#check NumStability.ThreeMMethodError
