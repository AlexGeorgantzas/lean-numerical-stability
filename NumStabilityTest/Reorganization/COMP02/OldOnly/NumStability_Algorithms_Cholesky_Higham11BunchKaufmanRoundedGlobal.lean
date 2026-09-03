import NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedGlobal

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedGlobal`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter11.BunchKaufman.Rounded.Global`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.Higham11RoundedBunchKaufmanExecution.flatProduct_case1_00
