import NumStability.Algorithms.Cholesky.Higham11RookSourceClosure

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.Cholesky.Higham11RookSourceClosure`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter11.Rook.SourceClosure`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.higham11_5_rookEliminatedCount_succ
