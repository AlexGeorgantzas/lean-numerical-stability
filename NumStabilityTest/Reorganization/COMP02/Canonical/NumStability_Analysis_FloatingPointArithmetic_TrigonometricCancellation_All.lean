import NumStability.Analysis.FloatingPointArithmetic.TrigonometricCancellation.All

/-! COMP-02 declaration-bearing isolation check for `NumStability.Analysis.FloatingPointArithmetic.TrigonometricCancellation.All`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Analysis.FloatingPointArithmetic.TrigonometricCancellation.Core`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.one_sub_cos_nonneg_exact
