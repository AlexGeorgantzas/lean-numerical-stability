import NumStability.Algorithms.Cholesky.AasenFactorNormCh11Closure

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.Cholesky.AasenFactorNormCh11Closure`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter11.AasenFactorNorm`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.Ch11Closure.AasenNorm.aasen_L_infNorm_le
