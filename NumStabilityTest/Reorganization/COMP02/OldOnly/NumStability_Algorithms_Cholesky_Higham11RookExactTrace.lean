import NumStability.Algorithms.Cholesky.Higham11RookExactTrace

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.Cholesky.Higham11RookExactTrace`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter11.Rook.ExactTrace`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.Higham11RookExecutorAdapter.higham11_5_exactMultTwo_one
