import NumStability.Algorithms.Cholesky.Higham11BunchKaufmanSourceCorrection

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.Cholesky.Higham11BunchKaufmanSourceCorrection`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter11.BunchKaufman.SourceCorrection`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.higham11_4_computed_productMax_le_of_relative_factor_bounds
