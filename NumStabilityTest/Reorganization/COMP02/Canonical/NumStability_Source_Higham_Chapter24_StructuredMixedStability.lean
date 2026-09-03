import NumStability.Source.Higham.Chapter24.StructuredMixedStability

/-! COMP-02 declaration-bearing isolation check for `NumStability.Source.Higham.Chapter24.StructuredMixedStability`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter24.StructuredMixedStability`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.higham24_mul_oneAddInverse
