import NumStability.Analysis.CancellationOfRoundingErrors

/-!
# CancellationOfRoundingErrors old-import test

Imports only the historical path, proving the retained compatibility
module still resolves the declarations it used to own.
-/

#check @NumStability.expm1LogRatio
#check @NumStability.expm1Table12X
#check @NumStability.expm1Table12_x_rows
