import NumStability.Algorithms.Summation.Tree.Core

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.Summation.Tree.Core`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Algorithms.Summation.Tree.Core`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.SumTree.n_pos
