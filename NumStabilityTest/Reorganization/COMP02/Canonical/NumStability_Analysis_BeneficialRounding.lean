import NumStability.Analysis.BeneficialRounding

/-! COMP-02 declaration-bearing isolation check for `NumStability.Analysis.BeneficialRounding`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Analysis.BeneficialRounding`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.vecNorm2_fin_sum_le
