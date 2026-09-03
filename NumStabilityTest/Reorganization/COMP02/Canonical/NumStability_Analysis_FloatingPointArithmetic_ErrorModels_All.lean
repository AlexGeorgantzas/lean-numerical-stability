import NumStability.Analysis.FloatingPointArithmetic.ErrorModels.All

/-! COMP-02 declaration-bearing isolation check for `NumStability.Analysis.FloatingPointArithmetic.ErrorModels.All`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Analysis.FloatingPointArithmetic.ErrorModels.Additive`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.noGuardAddWitness
