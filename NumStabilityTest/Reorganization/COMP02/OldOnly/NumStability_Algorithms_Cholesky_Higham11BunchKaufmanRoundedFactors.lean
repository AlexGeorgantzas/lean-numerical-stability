import NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedFactors

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedFactors`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter11.BunchKaufman.Rounded.Factors`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.higham11_2_liftPermTwo_one
