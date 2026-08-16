import NumStability.Source.Higham.Chapter11.Higham11SkewActualSelector

/-!
# R06 historical-only test — `Higham11SkewActualSelector`

Imports exactly the historical path; checks its preserved public
surface (18 declarations).
-/

#check @NumStability.higham11_9_firstColumnTailZero
#check @NumStability.higham11_9_skewActualPerm
#check @NumStability.higham11_9_skewActualPerm_injective
#check @NumStability.higham11_9_skewActualPermutedMatrix
#check @NumStability.higham11_9_skewActualPermutedMatrix_isSkew
#check @NumStability.higham11_9_skewActualPivotChoice_spec
#check @NumStability.higham11_9_skewActualPivotSize
#check @NumStability.higham11_9_skewPairArgmax
#check @NumStability.higham11_9_skewPairArgmax_indices_of_pos
#check @NumStability.higham11_9_skewPairArgmax_spec
#check @NumStability.higham11_9_skewPairScore
#check @NumStability.higham11_9_skewPivotMagnitude
#check @NumStability.higham11_9_skewPivotMagnitude_eq_abs_entry_of_pos
#check @NumStability.higham11_9_skewPivotMagnitude_pos_of_firstColumnTail_ne_zero
#check @NumStability.higham11_9_skewPivotP
#check @NumStability.higham11_9_skewPivotQ
#check @NumStability.higham11_9_skewPivot_dominates_column_one
#check @NumStability.higham11_9_skewPivot_dominates_column_zero
