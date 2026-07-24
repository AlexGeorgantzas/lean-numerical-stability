import NumStability.Source.Higham.Chapter14

/-!
# Canonical Chapter 14 aggregate import smoke test

The chapter umbrella exposes both the discrepancy record and the migrated
Section 14.5 Schulz family.
-/

#check NumStability.higham14_hadamardConditionNumberRaw_negative_one_counterexample
#check NumStability.higham14SchulzStep
#check NumStability.Ch14Ext.ch14ext_rectSchulzStep
#check NumStability.Ch14Ext.ch14ext_schulzIter_tendsto_inverse_of_lt_two_div_norm_sq
