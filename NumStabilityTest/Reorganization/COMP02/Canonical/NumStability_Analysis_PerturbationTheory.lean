import NumStability.Analysis.PerturbationTheory

/-! COMP-02 declaration-bearing isolation check for `NumStability.Analysis.PerturbationTheory`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Analysis.PerturbationTheory`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.abs_signInd
