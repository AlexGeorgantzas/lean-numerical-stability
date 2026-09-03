import NumStability.Algorithms.Cholesky.Higham11SkewSourceCorrection

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.Cholesky.Higham11SkewSourceCorrection`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter11.Skew.SourceCorrection`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.higham11_9_twoColumnCounterexample_skew
