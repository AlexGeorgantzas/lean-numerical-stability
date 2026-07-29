import NumStability.Algorithms.LeastSquares.LSQRSolve

/-!
# LSQRSolve historical import smoke test

Imports only the historical path, proving the retained compatibility
wrapper still resolves its original declarations.
-/

#check @NumStability.rectLSRhs
#check @NumStability.lsResidual
#check @NumStability.rectLSGram
