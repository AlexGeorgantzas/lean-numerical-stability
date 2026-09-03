import NumStability.Analysis.ComplexArithmetic

/-! COMP-02 declaration-bearing isolation check for `NumStability.Analysis.ComplexArithmetic`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Analysis.ComplexArithmetic`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.fl_complexAdd_error_bound
