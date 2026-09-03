import NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedClosure

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedClosure`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter11.BunchKaufman.Rounded.Closure`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.higham11_2_one_add_thirtySix_u_le_three
