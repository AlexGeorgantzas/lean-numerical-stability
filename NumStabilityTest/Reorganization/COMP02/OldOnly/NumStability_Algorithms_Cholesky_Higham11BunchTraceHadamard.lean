import NumStability.Algorithms.Cholesky.Higham11BunchTraceHadamard

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.Cholesky.Higham11BunchTraceHadamard`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter11.Bunch.TraceHadamard`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.one_le_bunchSharpGrowthBound
