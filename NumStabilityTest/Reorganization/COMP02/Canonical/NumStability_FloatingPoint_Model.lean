import NumStability.FloatingPoint.Model

/-! COMP-02 declaration-bearing isolation check for `NumStability.FloatingPoint.Model`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.FloatingPoint.Model`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.FPModel.model_basicOp
