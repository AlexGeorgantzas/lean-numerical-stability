import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.forwardSub_backward_error
