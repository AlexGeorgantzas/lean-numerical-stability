import NumStability.Source.Higham.Chapter11.BunchTridiagonalActualSolve

/-! COMP-02 declaration-bearing isolation check for `NumStability.Source.Higham.Chapter11.BunchTridiagonalActualSolve`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter11.BunchTridiagonalActualSolve`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.Ch11Closure.BunchTriActual.flBunchTwoByTwoSolve_one
