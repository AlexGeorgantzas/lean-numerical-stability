import NumStability.Algorithms.TestMatrices.Higham28PascalOscillationExact

/-!
# Higham28PascalOscillationExact old-path-only test

Imports only the historical path. Every declaration checked below moved to a
canonical module during wave W09, so this compiles only if the compatibility
module still re-exports it under its original name.

This owner is a declaration-bearing facade: its retained private closure
keeps these declarations here, so they are checked in place.
-/
#check @NumStability.pascalSortedEigenvector_signChangeCount_ge
#check @NumStability.pascalSortedEigenvector_hasExactlySignChanges
