import NumStability.Algorithms.LinearSystems.LeastSquares.RowSorting

/-!
# RowSorting canonical-only import smoke test

Imports exactly one canonical module so no sibling import can supply
the declarations checked below.
-/

#check @NumStability.Higham20EliminationActual.exactPivotedQRBeta
#check @NumStability.Higham20EliminationActual.exactPivotedQRPseq
#check @NumStability.Higham20EliminationActual.exactPivotedQRSwapSeq
