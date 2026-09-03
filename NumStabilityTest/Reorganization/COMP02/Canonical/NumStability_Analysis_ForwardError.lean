import NumStability.Analysis.ForwardError

/-! COMP-02 declaration-bearing isolation check for `NumStability.Analysis.ForwardError`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Analysis.ForwardError`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.backSub_forward_error
