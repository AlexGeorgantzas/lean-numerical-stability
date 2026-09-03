import NumStability.Algorithms.MatMul

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.MatMul`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Algorithms.MatMul`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.matMul_error_bound
