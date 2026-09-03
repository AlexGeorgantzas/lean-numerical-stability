import NumStability.Algorithms.Cholesky.Higham11BunchKaufmanExplicitInverseSolve

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.Cholesky.Higham11BunchKaufmanExplicitInverseSolve`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter11.BunchKaufman.ExplicitInverse.Solve`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.higham11_2_case4_selected_product_half_bound
