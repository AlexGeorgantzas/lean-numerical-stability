import NumStability.Analysis.Perturbation.LeastSquares.NormalEquations

/-!
# NormalEquations canonical-only import smoke test

Imports exactly one canonical module so no sibling import can supply
the declarations checked below.
-/

#check @NumStability.rectLSGramPerturbation
#check @NumStability.rectLSGramPerturbation_eq_sum
#check @NumStability.rectLSGramPerturbationNormBudget
