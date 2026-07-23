import NumStability.Source.Higham.Chapter25.Eigenproblem
import NumStability.Source.Higham.Chapter25.NonlinearSystems
import NumStability.Source.Higham.Chapter25.Problem01

/-!
# Canonical Chapter 25 import smoke test

Each implementation module is imported directly so the chapter umbrella cannot
mask an unresolved canonical path.
-/

#check NumStability.higham25EigenRoundedResidual
#check NumStability.higham25NewtonEquation
#check NumStability.higham25_problem25_1_A15
