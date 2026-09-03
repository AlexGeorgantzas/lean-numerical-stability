import NumStability.Source.Higham.Chapter24.RoundedDiagonalSolve

/-! COMP-02 declaration-bearing isolation check for `NumStability.Source.Higham.Chapter24.RoundedDiagonalSolve`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter24.RoundedDiagonalSolve`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.higham24_diagonalSolveRelativeError_spec
