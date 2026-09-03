import NumStability.Analysis.FloatingPointArithmetic.DoubleRounding.All

/-! COMP-02 declaration-bearing isolation check for `NumStability.Analysis.FloatingPointArithmetic.DoubleRounding.All`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Analysis.FloatingPointArithmetic.DoubleRounding.FiniteNormalRange`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.FloatingPointFormat.binaryT2DoubleRounding_21_16_finiteNormalRange
