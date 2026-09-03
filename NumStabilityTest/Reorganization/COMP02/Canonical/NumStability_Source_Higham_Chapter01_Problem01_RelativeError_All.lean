import NumStability.Source.Higham.Chapter01.Problem01.RelativeError.All

/-! COMP-02 declaration-bearing isolation check for `NumStability.Source.Higham.Chapter01.Problem01.RelativeError.All`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter01.Problem01.RelativeError.Bounds`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.problem_1_1_relError_bounds
