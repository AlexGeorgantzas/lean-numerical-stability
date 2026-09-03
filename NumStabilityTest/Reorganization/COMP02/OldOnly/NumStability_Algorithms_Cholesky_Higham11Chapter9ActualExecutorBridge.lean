import NumStability.Algorithms.Cholesky.Higham11Chapter9ActualExecutorBridge

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.Cholesky.Higham11Chapter9ActualExecutorBridge`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.CrossChapter.SymmetricIndefiniteLU.ActualExecutorBridge`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.higham11_7_permutedAbsLDLT_refl_eq_productEntry
