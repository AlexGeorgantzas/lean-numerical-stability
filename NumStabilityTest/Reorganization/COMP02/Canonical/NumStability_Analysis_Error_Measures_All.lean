import NumStability.Analysis.Error.Measures.All

/-! COMP-02 declaration-bearing isolation check for `NumStability.Analysis.Error.Measures.All`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Analysis.Error.Measures.AccuracyPrecision`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.fl_mul_relError_le_precision
