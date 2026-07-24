import NumStability.Source.Higham.Chapter04.Equation07.NoGuardCounterexample

/-!
# Higham equation (4.7) no-guard source-leaf smoke test

This test imports only the canonical source leaf for the concrete no-guard
counterexample.
-/

#check NumStability.noGuardCorrectionFormulaCounterexample_model
#check NumStability.noGuardCorrectionFormulaCounterexample_toCorrectionFormulaTrace_not_exact
