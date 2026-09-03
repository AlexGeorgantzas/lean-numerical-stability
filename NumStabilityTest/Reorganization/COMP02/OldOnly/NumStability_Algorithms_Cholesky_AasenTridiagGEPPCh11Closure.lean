import NumStability.Algorithms.Cholesky.AasenTridiagGEPPCh11Closure

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.Cholesky.AasenTridiagGEPPCh11Closure`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter11.AasenTridiagGEPP`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.Ch11Closure.AasenDirect.bunchAbsFactorProduct_nonneg
