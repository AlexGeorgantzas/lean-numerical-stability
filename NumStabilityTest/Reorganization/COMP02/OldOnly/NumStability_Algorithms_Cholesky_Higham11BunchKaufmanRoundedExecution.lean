import NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedExecution

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedExecution`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter11.BunchKaufman.Rounded.Execution`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.higham11_2_bunchKaufmanTrailingRhs_eq_active
