import NumStability.Algorithms.LinearSystems.LU.BlockLU.FirstOrderModels

/-!
# Block-LU first-order models import smoke test

This test imports only the canonical declaration-bearing leaf and checks all
thirteen reviewed source command roots.
-/

#check NumStability.MatMulFirstOrderBound
#check NumStability.MatMulFirstOrderSpec
#check NumStability.TriangularSolveFirstOrderBound
#check NumStability.TriangularSolveFirstOrderSpec
#check NumStability.RightTriangularSolveFirstOrderSpec
#check NumStability.LocalLUFirstOrderBound
#check NumStability.LocalLUFirstOrderSpec
#check NumStability.SubtractionFirstOrderSpec
#check NumStability.PartitionedLUFirstOrderSpec
#check NumStability.BlockSolveFirstOrderBound
#check NumStability.BlockSolveFirstOrderSpec
#check NumStability.DiagonalBlockSolveFirstOrderBound
#check NumStability.DiagonalBlockSolveFirstOrderSpec
