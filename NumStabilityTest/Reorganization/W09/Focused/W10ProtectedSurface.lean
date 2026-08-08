import NumStability.Algorithms.TestMatrices.Higham28OrthogonalCoordinates

/-!
# W10ProtectedSurface: accepted dependency boundary

W10 consumes four W09 owners through `Higham28OrthogonalCoordinates` across 28 signature and 48 body edges. W09 does not edit W10; it keeps that surface resolvable from the historical path, so a lost re-export fails here.
-/
