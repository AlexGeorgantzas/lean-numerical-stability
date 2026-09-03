import NumStability.Algorithms.LU.GaussianElimination

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.LU.GaussianElimination`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Algorithms.LU.GaussianElimination`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.nonneg_factor_bound
