import NumStability.Upstream.Lindemann.Basic

/-! COMP-02 declaration-bearing isolation check for `NumStability.Upstream.Lindemann.Basic`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Upstream.Lindemann.Basic`; a break in the forwarding chain makes this file fail.
-/

#check @transcendental_e
