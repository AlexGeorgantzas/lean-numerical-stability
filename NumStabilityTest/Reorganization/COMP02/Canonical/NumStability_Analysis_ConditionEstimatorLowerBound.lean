import NumStability.Analysis.ConditionEstimatorLowerBound

/-! COMP-02 declaration-bearing isolation check for `NumStability.Analysis.ConditionEstimatorLowerBound`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Analysis.ConditionEstimatorLowerBound`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.condOneNumber_nonneg
