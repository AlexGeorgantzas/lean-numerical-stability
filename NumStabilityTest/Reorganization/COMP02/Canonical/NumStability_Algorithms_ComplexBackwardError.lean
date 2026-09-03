import NumStability.Algorithms.ComplexBackwardError

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.ComplexBackwardError`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Algorithms.ComplexBackwardError`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.complexMatVec_backward_error
