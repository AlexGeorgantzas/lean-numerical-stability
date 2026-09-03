import NumStability.Algorithms.Cholesky.AasenGrowthCh11Closure

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.Cholesky.AasenGrowthCh11Closure`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter11.AasenGrowth`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.Ch11Closure.Aasen.aasenH_row_bound
