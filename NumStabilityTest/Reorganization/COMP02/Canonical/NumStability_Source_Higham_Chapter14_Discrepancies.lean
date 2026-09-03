import NumStability.Source.Higham.Chapter14.Discrepancies

/-! COMP-02 declaration-bearing isolation check for `NumStability.Source.Higham.Chapter14.Discrepancies`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter14.Discrepancies`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.higham14_hadamardConditionNumberRaw_negative_one_counterexample
