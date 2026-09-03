import NumStability.Analysis.Nonassociativity

/-! COMP-02 declaration-bearing isolation check for `NumStability.Analysis.Nonassociativity`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Analysis.Nonassociativity`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.FloatingPointFormat.decimalOneDigitTwoExponent_add_ten_zero_exact
