import NumStability.Algorithms.Cholesky.AasenOriginalCoordinateCorrectionCh11

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.Cholesky.AasenOriginalCoordinateCorrectionCh11`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter11.AasenOriginalCoordinateCorrection`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.Ch11Closure.AasenAdjacentOperational.aasenUnpermuteMatrix_infNorm
