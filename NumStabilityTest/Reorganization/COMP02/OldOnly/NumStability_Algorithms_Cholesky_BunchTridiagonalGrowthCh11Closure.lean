import NumStability.Algorithms.Cholesky.BunchTridiagonalGrowthCh11Closure

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.Cholesky.BunchTridiagonalGrowthCh11Closure`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Algorithms.LinearSystems.SymmetricIndefinite.BlockLDLT.BunchTridiagonalGrowth`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.Ch11Closure.BunchTriGrowth.flMixedMult2_corner0
