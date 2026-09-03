import NumStability.Source.Higham.Chapter11.AasenPrintedCoefficientAlgebra

/-! COMP-02 declaration-bearing isolation check for `NumStability.Source.Higham.Chapter11.AasenPrintedCoefficientAlgebra`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter11.AasenPrintedCoefficientAlgebra`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.Ch11Closure.AasenPrinted.factor_plus_chain_le_printed
