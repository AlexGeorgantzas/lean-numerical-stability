import NumStability.Analysis.Problem2_26

/-!
# Problem2_26 old-import test

Imports only the historical path. The declarations below moved to canonical
modules during wave W12, so this compiles only if the compatibility module
still re-exports them at their original names.
-/

#check @NumStability.reciprocalNewtonStep
#check @NumStability.reciprocalNewtonStepIter
#check @NumStability.reciprocalNewtonCorrection
