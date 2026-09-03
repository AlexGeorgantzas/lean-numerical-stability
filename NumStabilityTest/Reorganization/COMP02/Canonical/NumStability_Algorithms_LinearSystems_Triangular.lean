import NumStability.Algorithms.LinearSystems.Triangular

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.LinearSystems.Triangular`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.backSub_row_tight
