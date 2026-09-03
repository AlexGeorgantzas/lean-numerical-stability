import NumStability.Algorithms.MMatrix

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.MMatrix`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Algorithms.MMatrix`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.forwardSub_nonneg
