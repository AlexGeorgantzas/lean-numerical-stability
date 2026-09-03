import NumStability.Algorithms.Cholesky.Higham11BunchActualSharpGrowthClosure

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.Cholesky.Higham11BunchActualSharpGrowthClosure`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter11.Bunch.ActualSharpGrowthClosure`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.higham11_1_one_le_bunchSharpGrowthBound
