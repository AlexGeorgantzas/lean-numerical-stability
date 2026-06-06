import LeanFpAnalysis.HDP.Probability.Concentration.Basic
import LeanFpAnalysis.HDP.Probability.Concentration.Hoeffding
import LeanFpAnalysis.HDP.Probability.Concentration.Chernoff
import LeanFpAnalysis.HDP.Probability.Concentration.Normal
import LeanFpAnalysis.HDP.Probability.Concentration.BerryEsseen
import LeanFpAnalysis.HDP.Probability.Concentration.BerryEsseenSmoothing
import LeanFpAnalysis.HDP.Probability.Concentration.Applications
import LeanFpAnalysis.HDP.Probability.Concentration.Poisson

/-!
# Concentration Inequalities

Aggregates the HDP Chapter 2 concentration material formalized so far, including
the completed Berry-Esseen theorem with constant `C = 3` and the retained
Prawitz/Shevtsova bridge API for the later exact `C = 1` proof.
-/
