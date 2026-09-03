import NumStability.Algorithms.Summation.PlusMinus

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.Summation.PlusMinus`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Algorithms.Summation.PlusMinus`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.positivePart_nonneg
