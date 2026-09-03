import NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedGrowthSolve

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedGrowthSolve`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter11.BunchKaufman.Rounded.GrowthSolve`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.Higham11RoundedBunchKaufmanExecution.computedSolve_backward_error_normwise_forty
