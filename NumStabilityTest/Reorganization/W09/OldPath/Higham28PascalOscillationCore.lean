import NumStability.Algorithms.TestMatrices.Higham28PascalOscillationCore

/-!
# Higham28PascalOscillationCore old-path-only test

Imports only the historical path. Every declaration checked below moved to a
canonical module during wave W09, so this compiles only if the compatibility
module still re-exports it under its original name.
-/
#check @NumStability.boolSignChangeCount_not
#check @NumStability.boolSignChangeCount_extract
#check @NumStability.pascalOscillationBoolToSign
