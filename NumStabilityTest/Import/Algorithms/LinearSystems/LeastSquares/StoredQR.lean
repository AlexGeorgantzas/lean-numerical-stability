import NumStability.Algorithms.LinearSystems.LeastSquares.StoredQR

/-!
# StoredQR canonical-only import smoke test

Imports exactly one canonical module so no sibling import can supply
the declarations checked below.
-/

#check @NumStability.storedQRFinalR
#check @NumStability.storedQRFinalTopRhs
#check @NumStability.storedQRBackSubSolution
