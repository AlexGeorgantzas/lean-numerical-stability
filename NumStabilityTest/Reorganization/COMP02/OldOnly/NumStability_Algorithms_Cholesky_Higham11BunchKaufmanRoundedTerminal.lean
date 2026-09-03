import NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedTerminal

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedTerminal`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter11.BunchKaufman.Rounded.Terminal`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.Higham11RoundedBunchKaufmanExecution.computedSolve_backward_error_normwise_forty_actual
