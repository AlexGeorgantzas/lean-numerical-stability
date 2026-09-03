import NumStability.Source.Higham.Chapter11.Section01.Basic

/-! COMP-02 declaration-bearing isolation check for `NumStability.Source.Higham.Chapter11.Section01.Basic`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter11.Section01.Basic`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.higham11_3_blockLDLT_assemble_step
