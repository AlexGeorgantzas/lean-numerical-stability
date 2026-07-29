import NumStability.Algorithms.LinearSystems.LeastSquares.QRSolve

/-!
# QRSolve canonical-only import smoke test

Imports exactly one canonical module so no sibling import can supply
the declarations checked below.
-/

#check @NumStability.storedHouseholderQRRhsSeq
#check @NumStability.storedHouseholderQRAlphaSeq
#check @NumStability.storedHouseholderQRMatrixSeq
