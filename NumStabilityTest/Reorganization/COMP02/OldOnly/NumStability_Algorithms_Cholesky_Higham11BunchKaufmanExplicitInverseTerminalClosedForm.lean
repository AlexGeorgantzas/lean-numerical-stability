import NumStability.Algorithms.Cholesky.Higham11BunchKaufmanExplicitInverseTerminalClosedForm

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.Cholesky.Higham11BunchKaufmanExplicitInverseTerminalClosedForm`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter11.BunchKaufman.ExplicitInverse.TerminalClosedForm`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.Higham11RoundedBunchKaufmanExecution.solveResidualCoefficient_threeHundredSixty_mul_u_le_linear_add_quadratic
