import NumStability.Algorithms.Cholesky.AasenCoupledFpCh11Closure

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.Cholesky.AasenCoupledFpCh11Closure`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Algorithms.LinearSystems.SymmetricIndefinite.Aasen.AasenCoupledFp`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.Ch11Closure.AasenDirect.flAasen_T_band
