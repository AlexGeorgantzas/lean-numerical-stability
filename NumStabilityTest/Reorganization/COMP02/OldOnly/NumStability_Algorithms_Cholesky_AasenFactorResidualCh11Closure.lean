import NumStability.Algorithms.Cholesky.AasenFactorResidualCh11Closure

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.Cholesky.AasenFactorResidualCh11Closure`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Algorithms.LinearSystems.SymmetricIndefinite.Aasen.AasenFactorResidual`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.Ch11Closure.AasenDirect.absMulTheta_le
