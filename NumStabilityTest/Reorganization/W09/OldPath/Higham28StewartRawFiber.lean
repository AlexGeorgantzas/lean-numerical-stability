import NumStability.Algorithms.TestMatrices.Higham28StewartRawFiber

/-!
# Higham28StewartRawFiber old-path-only test

Imports only the historical path. Every declaration checked below moved to a
canonical module during wave W09, so this compiles only if the compatibility
module still re-exports it under its original name.
-/
#check @NumStability.stewartRawFiberMeasure
#check @NumStability.stewartRawFiberProducer
#check @NumStability.orthogonalFirstRow_stewartFirstSection_of_ne_zero
