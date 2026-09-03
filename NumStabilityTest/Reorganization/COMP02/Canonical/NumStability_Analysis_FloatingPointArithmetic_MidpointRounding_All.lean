import NumStability.Analysis.FloatingPointArithmetic.MidpointRounding.All

/-! COMP-02 declaration-bearing isolation check for `NumStability.Analysis.FloatingPointArithmetic.MidpointRounding.All`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Analysis.FloatingPointArithmetic.MidpointRounding.DecimalTieExamples`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.FloatingPointFormat.decimalOneDigitThreeExponent_div_one_two_exact
