import NumStability.Algorithms.Cholesky.BunchKaufmanSolveCh11Closure

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.Cholesky.BunchKaufmanSolveCh11Closure`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter11.BunchKaufmanSolve`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.Ch11Closure.BunchKaufman.higham11_4_bunch_kaufman_solve_backward_error_printed
