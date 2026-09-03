import NumStability.Source.Higham.Chapter01.Section07.Cancellation.All

/-! COMP-02 declaration-bearing isolation check for `NumStability.Source.Higham.Chapter01.Section07.Cancellation.All`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter01.Section07.Cancellation.Basic`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.subtract_perturbed_error_eq
