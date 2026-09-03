import NumStability.Algorithms.MatVec

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.MatVec`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Algorithms.MatVec`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.matVec_error_bound
