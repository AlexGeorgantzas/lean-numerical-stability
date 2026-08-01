import NumStability.Analysis.FloatingPointArithmetic

/-!
# FloatingPointArithmetic old-import test

Imports only the historical path, proving the retained compatibility
module still resolves the declarations it used to own.
-/

#check @NumStability.IeeeValue
#check @NumStability.IeeeValue.isNaN
#check @NumStability.IeeeRoundingMode
