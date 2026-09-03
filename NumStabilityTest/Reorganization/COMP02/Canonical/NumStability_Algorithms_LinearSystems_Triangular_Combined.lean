import NumStability.Algorithms.LinearSystems.Triangular.Combined

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.LinearSystems.Triangular.Combined`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Algorithms.LinearSystems.Triangular.Combined`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.triangularSolve_backward_error
