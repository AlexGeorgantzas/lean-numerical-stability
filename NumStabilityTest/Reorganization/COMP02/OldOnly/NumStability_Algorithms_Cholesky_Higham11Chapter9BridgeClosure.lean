import NumStability.Algorithms.Cholesky.Higham11Chapter9BridgeClosure

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.Cholesky.Higham11Chapter9BridgeClosure`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.CrossChapter.SymmetricIndefiniteLU.BridgeClosure`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.higham11_7_abs_matMul_le
