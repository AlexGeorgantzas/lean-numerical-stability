import NumStability.Algorithms.LeastSquares.LSNormalEquations

/-!
# LSNormalEquations historical import smoke test

Imports only the historical path, proving the retained compatibility
wrapper still resolves declarations from both canonical owners.
-/

#check @NumStability.RectLSNormalEquations
#check @NumStability.GramProductError
#check @NumStability.normalEqCholeskyGramBound
