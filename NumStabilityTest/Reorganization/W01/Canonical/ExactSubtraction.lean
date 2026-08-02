import NumStability.Analysis.FloatingPointArithmetic.ExactSubtraction

/-!
# Exact-subtraction reusable-import test

Imports exactly the reusable exact-subtraction module so no source wrapper or
sibling module can supply the checked declarations.
-/

#check @NumStability.FloatingPointFormat.sterbenzRatioCondition_symm
#check @NumStability.FloatingPointFormat.guardDigitLeadingDigit
