import NumStability.Algorithms.LU.LUSolve

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.LU.LUSolve`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Algorithms.LU.LUSolve`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.lu_solve_backward_error
