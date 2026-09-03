import NumStability.FloatingPoint.OperationLaws

/-! COMP-02 declaration-bearing isolation check for `NumStability.FloatingPoint.OperationLaws`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.FloatingPoint.OperationLaws`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.FloatingPointFormat.finiteRoundToEvenOp_add_comm
