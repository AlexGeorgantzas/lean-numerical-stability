import NumStability.Algorithms.LU.TridiagonalCond

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.LU.TridiagonalCond`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Algorithms.LU.TridiagonalCond`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.tridiag_exact_inv_abs
