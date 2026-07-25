import NumStability.Analysis.HighamChapter2PowerLeadingDigits

/-!
# Historical Higham Chapter 2 power-leading-digits import smoke test

Checks the old two-target wrapper independently of the canonical analysis and
source aggregates.
-/

#check NumStability.finUniformProbability
#check NumStability.orbit_mem_decimalDigitArc_iff
#check NumStability.higham2_power_decimalLeadingDigit_frequency_tendsto
#check NumStability.problem2_11EmpiricalSource
#check NumStability.problem2_11_empiricalDigitProbability
#check NumStability.logarithmicLeadingDigitMass
