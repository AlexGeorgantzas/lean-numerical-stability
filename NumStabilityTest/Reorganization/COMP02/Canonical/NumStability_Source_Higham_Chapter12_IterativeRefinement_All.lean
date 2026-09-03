import NumStability.Source.Higham.Chapter12.IterativeRefinement.All

/-! COMP-02 declaration-bearing isolation check for `NumStability.Source.Higham.Chapter12.IterativeRefinement.All`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter12.IterativeRefinement.ForwardErrorBounds.Results`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.forward_error_step_bound
