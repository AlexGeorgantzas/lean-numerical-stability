import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.LU.Doolittle
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve

/-!
# ProtectedW02Surface: accepted dependency boundary

The accepted W02 historical owners W08 imports directly. B0007 requires the boundary preserved exactly: 345 signature edges, 512 body/proof edges and 542 union pairs across sixteen direct imports. This test pins that those modules still resolve from a W08-adjacent context.
-/
