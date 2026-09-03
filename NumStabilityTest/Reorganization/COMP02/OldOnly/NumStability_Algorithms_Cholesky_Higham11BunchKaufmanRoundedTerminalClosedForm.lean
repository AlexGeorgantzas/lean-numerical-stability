import NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedTerminalClosedForm

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedTerminalClosedForm`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter11.BunchKaufman.Rounded.TerminalClosedForm`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.Higham11RoundedBunchKaufmanExecution.completed_of_middleSolveRunDomain
