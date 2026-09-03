import NumStability.Algorithms.Cholesky.Higham11BunchSharpGrowthBridge

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.Cholesky.Higham11BunchSharpGrowthBridge`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter11.Bunch.SharpGrowthBridge`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.Higham11BunchSharpBlock.width_pos
