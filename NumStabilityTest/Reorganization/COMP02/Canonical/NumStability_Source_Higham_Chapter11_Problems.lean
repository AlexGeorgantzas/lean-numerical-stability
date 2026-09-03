import NumStability.Source.Higham.Chapter11.Problems

/-! COMP-02 declaration-bearing isolation check for `NumStability.Source.Higham.Chapter11.Problems`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter11.Problems`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.higham11_problem_11_9_nonsymPosDef_of_symPartSPD
