import NumStability.Algorithms.DotProduct

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.DotProduct`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Algorithms.DotProduct`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.dotProduct_error_bound
