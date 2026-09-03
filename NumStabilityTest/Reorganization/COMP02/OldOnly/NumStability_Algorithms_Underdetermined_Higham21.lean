import NumStability.Algorithms.Underdetermined.Higham21

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.Underdetermined.Higham21`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Algorithms.LinearSystems.QR.HouseholderQApply`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.matMulVec_embedTrailingOne_eq_finCons
