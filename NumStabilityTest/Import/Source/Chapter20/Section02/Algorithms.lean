import NumStability.Source.Higham.Chapter20.Section02.Algorithms

/-!
# Section02.Algorithms canonical-only import smoke test

Imports exactly one canonical module so no sibling import can supply
the declarations checked below.
-/

#check @NumStability.higham20_qrFactorization_rectLSGram_eq_seminormalGram
#check @NumStability.Higham20SeminormalEquationsSolve.isLeastSquaresMinimizer_of_qr
#check @NumStability.Higham20AugmentedRefinementStep.updated_isLeastSquaresMinimizer
