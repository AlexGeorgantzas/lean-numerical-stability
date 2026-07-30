import NumStability.Algorithms.LeastSquares.Higham20EliminationActual

/-!
# Higham20EliminationActual historical import smoke test

Imports only the historical path, proving the retained compatibility
wrapper still resolves its original declarations.
-/

#check @NumStability.Higham20EliminationActual.pivotDAacc_zero
#check @NumStability.Higham20EliminationActual.exactPivotedQRBeta
#check @NumStability.Higham20EliminationActual.exactPivotedQRPseq
