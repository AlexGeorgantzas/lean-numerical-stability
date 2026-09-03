import NumStability.Algorithms.Cholesky.AasenDirect118Ch11Closure

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.Cholesky.AasenDirect118Ch11Closure`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter11.AasenDirect118`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.Ch11Closure.AasenDirect.infNorm_const_mul_le
