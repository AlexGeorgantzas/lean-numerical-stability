import NumStability.Source.Higham.Chapter11.BunchKaufmanSolve

/-! COMP-02 declaration-bearing isolation check for `NumStability.Source.Higham.Chapter11.BunchKaufmanSolve`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter11.BunchKaufmanSolve`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.Ch11Closure.BunchKaufman.higham11_4_bunch_kaufman_solve_backward_error_printed
