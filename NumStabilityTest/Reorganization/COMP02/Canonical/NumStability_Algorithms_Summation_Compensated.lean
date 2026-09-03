import NumStability.Algorithms.Summation.Compensated

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.Summation.Compensated`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Algorithms.Summation.Compensated.CorrectionFormula`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.correctionFormulaTrace_e
